package org.checkerframework.specimin;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.google.common.base.Splitter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * The main visitor for Specimin's first phase, which locates the target method(s) and compiles
 * information on what specifications they use.
 */
public class TargetMethodFinderVisitor extends ModifierVisitor<Void> {
  /**
   * The names of the target methods. The format is
   * class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...). All the names will have
   * spaces remove for ease of comparison.
   */
  private Set<String> targetMethodNames;

  /** The names of the target fields. The format is class.fully.qualified.Name#fieldName. */
  private Set<String> targetFieldNames;

  /**
   * This boolean tracks whether the element currently being visited is inside a target method. It
   * is set by {@link #visit(MethodDeclaration, Void)}.
   */
  private boolean insideTargetMember = false;

  /** The fully-qualified name of the class currently being visited. */
  private String classFQName = "";

  /** The name of the package currently being visited. */
  private String currentPackage = "";

  /**
   * The members (methods and fields) that were actually used by the targets, and therefore ought to
   * have their specifications (but not bodies) preserved. The Strings in the set are the
   * fully-qualified names, as returned by ResolvedMethodDeclaration#getQualifiedSignature for
   * methods and FieldAccessExpr#getName for fields.
   */
  private final Set<String> usedMembers = new HashSet<>();

  /**
   * Type elements (classes, interfaces, and enums) related to the methods used by the targets.
   * These classes will be included in the input.
   */
  private Set<String> usedTypeElement = new HashSet<>();

  /** Set of variables declared in this current class */
  private final Set<String> declaredNames = new HashSet<>();

  /**
   * The resolved target methods. The Strings in the set are the fully-qualified names, as returned
   * by ResolvedMethodDeclaration#getQualifiedSignature.
   */
  private final Set<String> targetMethods = new HashSet<>();

  /**
   * The keys of this map are a local copy of the input list of methods. A method is removed from
   * this copy's key set when it is located. If the visitor has been run on all source files and the
   * key set isn't empty, that usually indicates an error. The values are other method signatures
   * that were found in the key's class, but which were not the key. These values are only used for
   * error reporting: it is useful to the user if they make a typo to know what the correct
   * name/signature of a method actually is.
   */
  private final Map<String, Set<String>> unfoundMethods;

  /**
   * This map has the name of an imported class as key and the package of that class as the value.
   */
  private final Map<String, String> importedClassToPackage;

  /**
   * This map connects the resolved declaration of a method to the interface that contains it, if
   * any.
   */
  private final Map<ResolvedMethodDeclaration, ClassOrInterfaceType>
      methodDeclarationToInterfaceType = new HashMap<>();

  /**
   * This map connects the fully-qualified names of non-primary classes with the fully-qualified
   * names of their corresponding primary classes. A primary class is a class that has the same name
   * as the Java file where the class is declared.
   */
  Map<String, String> nonPrimaryClassesToPrimaryClass;

  /**
   * JavaParser is not perfect. Sometimes it can't solve resolved method calls if they have
   * complicated type variables or if the receiver is the parameter of a lambda expression. We keep
   * track of these stuck method calls and preserve them anyway. There are two possible formats for
   * the strings in this set: fully-qualified method names (which will be directly preserved) and
   * unqualified method names with a {@literal @} symbol and the number of parameters that they take
   * appended. Anything that matches the latter will later be preserved.
   */
  private final Set<String> resolvedYetStuckMethodCall = new HashSet<>();

  /**
   * Create a new target method finding visitor.
   *
   * @param methodNames the names of the target methods, the format
   *     class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
   * @param fieldNames the names of the target fields, the format is
   *     class.fully.qualified.Name#fieldName
   * @param nonPrimaryClassesToPrimaryClass map connecting non-primary classes with their
   *     corresponding primary classes
   * @param usedTypeElement set of type elements used by target methods.
   */
  public TargetMethodFinderVisitor(
      List<String> methodNames,
      List<String> fieldNames,
      Map<String, String> nonPrimaryClassesToPrimaryClass,
      Set<String> usedTypeElement) {
    targetMethodNames = new HashSet<>();
    for (String methodSignature : methodNames) {
      this.targetMethodNames.add(methodSignature.replaceAll("\\s", ""));
    }
    targetFieldNames = new HashSet<>();
    targetFieldNames.addAll(fieldNames);
    unfoundMethods = new HashMap<>(methodNames.size());
    targetMethodNames.forEach(m -> unfoundMethods.put(m, new HashSet<>()));
    importedClassToPackage = new HashMap<>();
    this.nonPrimaryClassesToPrimaryClass = nonPrimaryClassesToPrimaryClass;
    this.usedTypeElement = usedTypeElement;
  }

  /**
   * Returns the methods that so far this visitor has not located from its target list. Usually,
   * this should be checked after running the visitor to ensure that it is empty. The targets are
   * the keys in the returned maps; the values are methods in the same class that were considered
   * but were not the target (useful for issuing error messages).
   *
   * @return the methods that so far this visitor has not located from its target list, mapped to
   *     the candidate methods that were considered
   */
  public Map<String, Set<String>> getUnfoundMethods() {
    return unfoundMethods;
  }

  /**
   * Get the methods that this visitor has concluded that the target method(s) use, and therefore
   * ought to be retained. The Strings in the set are the fully-qualified names, as returned by
   * ResolvedMethodDeclaration#getQualifiedSignature.
   *
   * @return the used methods
   */
  public Set<String> getUsedMembers() {
    return usedMembers;
  }

  /**
   * Get the classes of the methods and enums that the target method uses. The Strings in the set
   * are the fully-qualified names.
   *
   * @return the used type elements.
   */
  public Set<String> getUsedTypeElement() {
    return usedTypeElement;
  }

  /**
   * Get the target methods that this visitor has encountered so far. The Strings in the set are the
   * fully-qualified names, as returned by ResolvedMethodDeclaration#getQualifiedSignature.
   *
   * @return the target methods
   */
  public Set<String> getTargetMethods() {
    return targetMethods;
  }

  /**
   * Get the set of resolved yet stuck method calls.
   *
   * @return the value of stuck methods.
   */
  public Set<String> getResolvedYetStuckMethodCall() {
    return resolvedYetStuckMethodCall;
  }

  /**
   * Updates the mapping of method declarations to their corresponding interface type based on a
   * list of methods and the interface type that contains those methods.
   *
   * @param methodList the list of resolved method declarations
   * @param interfaceType the interface containing the specified methods.
   */
  private void updateMethodDeclarationToInterfaceType(
      List<ResolvedMethodDeclaration> methodList, ClassOrInterfaceType interfaceType) {
    for (ResolvedMethodDeclaration method : methodList) {
      this.methodDeclarationToInterfaceType.put(method, interfaceType);
    }
  }

  /**
   * Updates unfoundMethods so that the appropriate elements have their set of considered methods
   * updated to match a method that was not a target method.
   *
   * @param methodAsString the method that wasn't a target method
   */
  private void updateUnfoundMethods(String methodAsString) {
    Set<String> targetMethodsInClass =
        targetMethodNames.stream()
            .filter(t -> t.startsWith(this.classFQName))
            .collect(Collectors.toSet());

    for (String targetMethodInClass : targetMethodsInClass) {
      // This check is necessary to avoid an NPE if the target method
      // in question has already been removed from unfoundMethods.
      if (unfoundMethods.containsKey(targetMethodInClass)) {
        unfoundMethods.get(targetMethodInClass).add(methodAsString);
      }
    }
  }

  @Override
  public Visitable visit(PackageDeclaration decl, Void p) {
    this.currentPackage = decl.getNameAsString();
    return super.visit(decl, p);
  }

  @Override
  public Node visit(ImportDeclaration decl, Void p) {
    String classFullName = decl.getNameAsString();
    if (decl.isStatic()) {
      classFullName = classFullName.substring(0, classFullName.lastIndexOf("."));
    }
    String classSimpleName = classFullName.substring(classFullName.lastIndexOf(".") + 1);
    String packageName = classFullName.replace("." + classSimpleName, "");
    importedClassToPackage.put(classSimpleName, packageName);
    return super.visit(decl, p);
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
    for (ClassOrInterfaceType interfaceType : decl.getImplementedTypes()) {
      try {
        updateMethodDeclarationToInterfaceType(
            JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(interfaceType)
                .getAllMethods(),
            interfaceType);
      } catch (UnsolvedSymbolException e) {
        continue;
      }
    }

    processAnnotations(decl.getAnnotations());

    manageClassFQNamePreSuper(decl);
    Visitable result = super.visit(decl, p);
    manageClassFQNamePostSuper(decl);
    return result;
  }

  @Override
  public Visitable visit(EnumDeclaration decl, Void p) {
    processAnnotations(decl.getAnnotations());

    manageClassFQNamePreSuper(decl);
    Visitable result = super.visit(decl, p);
    manageClassFQNamePostSuper(decl);
    return result;
  }

  /**
   * Helper method to share code for managing the {@link #classFQName} field between
   * classes/interfaces and enums. Call this method before calling super.visit().
   *
   * @see #classFQName
   * @see #manageClassFQNamePostSuper(TypeDeclaration)
   * @param decl a class, interface, or enum declaration
   */
  private void manageClassFQNamePreSuper(TypeDeclaration<?> decl) {
    if (decl.isNestedType()) {
      this.classFQName += "." + decl.getName().toString();
    } else {
      if (!JavaParserUtil.isLocalClassDecl(decl)) {
        if (!"".equals(this.classFQName)) {
          throw new UnsupportedOperationException(
              "Attempted to enter an unexpected kind of class: "
                  + decl.getFullyQualifiedName()
                  + " but already had a set classFQName: "
                  + classFQName);
        }
        // Should always be present.
        this.classFQName = decl.getFullyQualifiedName().orElseThrow();
      }
    }
  }

  /**
   * Helper method to share code for managing the {@link #classFQName} field between
   * classes/interfaces and enums. Call this method after calling super.visit().
   *
   * @see #classFQName
   * @see #manageClassFQNamePreSuper(TypeDeclaration)
   * @param decl a class, interface, or enum declaration
   */
  private void manageClassFQNamePostSuper(TypeDeclaration<?> decl) {
    if (decl.isNestedType()) {
      this.classFQName = this.classFQName.substring(0, this.classFQName.lastIndexOf('.'));
    } else if (!JavaParserUtil.isLocalClassDecl(decl)) {
      this.classFQName = "";
    }
  }

  @Override
  public Visitable visit(ConstructorDeclaration method, Void p) {
    String constructorMethodAsString = method.getDeclarationAsString(false, false, false);
    // the methodName will be something like this: "com.example.Car#Car()"
    String methodName = this.classFQName + "#" + constructorMethodAsString;
    boolean oldInsideTargetMember = insideTargetMember;
    if (this.targetMethodNames.contains(methodName)) {
      insideTargetMember = true;
      ResolvedConstructorDeclaration resolvedMethod = method.resolve();
      targetMethods.add(resolvedMethod.getQualifiedSignature());
      unfoundMethods.remove(methodName);
      updateUsedClassWithQualifiedClassName(
          resolvedMethod.getPackageName() + "." + resolvedMethod.getClassName(),
          usedTypeElement,
          nonPrimaryClassesToPrimaryClass);

      processAnnotations(method.getAnnotations());
    } else {
      updateUnfoundMethods(methodName);
    }

    Visitable result = super.visit(method, p);
    insideTargetMember = oldInsideTargetMember;

    if (method.getParentNode().isEmpty()) {
      return result;
    }
    if (method.getParentNode().get() instanceof EnumDeclaration) {
      EnumDeclaration parentNode = (EnumDeclaration) method.getParentNode().get();
      if (parentNode.getFullyQualifiedName().isEmpty()) {
        return result;
      }
      // used enums needs to have compilable constructors.
      if (usedTypeElement.contains(parentNode.getFullyQualifiedName().orElseThrow())) {
        for (Parameter parameter : method.getParameters()) {
          updateUsedClassBasedOnType(parameter.getType().resolve());
        }
      }
    }
    return result;
  }

  @Override
  public Visitable visit(VariableDeclarator node, Void arg) {
    declaredNames.add(node.getNameAsString());

    if (node.getParentNode().isPresent()
        && node.getParentNode().get() instanceof FieldDeclaration) {
      if (targetFieldNames.contains(this.classFQName + "#" + node.getNameAsString())) {
        boolean oldInsideTargetMember = insideTargetMember;
        insideTargetMember = true;
        Visitable result = super.visit(node, arg);
        usedTypeElement.add(this.classFQName);
        insideTargetMember = oldInsideTargetMember;

        processAnnotations(((FieldDeclaration) node.getParentNode().get()).getAnnotations());

        return result;
      }
    }
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(MethodDeclaration method, Void p) {
    boolean oldInsideTargetMember = insideTargetMember;
    String methodDeclAsString = method.getDeclarationAsString(false, false, false);
    // TODO: test this with annotations
    String methodWithoutReturnAndAnnos = removeMethodReturnTypeAndAnnotations(methodDeclAsString);
    String methodName = this.classFQName + "#" + methodWithoutReturnAndAnnos;
    // this method belongs to an anonymous class inside the target method
    if (insideTargetMember) {
      Node parentNode = method.getParentNode().get();
      // it could also be an enum declaration, but those are handled separately
      if (parentNode instanceof ObjectCreationExpr) {
        ObjectCreationExpr parentExpression = (ObjectCreationExpr) parentNode;
        ResolvedConstructorDeclaration resolved = parentExpression.resolve();
        String methodPackage = resolved.getPackageName();
        String methodClass = resolved.getClassName();
        usedMembers.add(methodPackage + "." + methodClass + "." + method.getNameAsString() + "()");
        updateUsedClassWithQualifiedClassName(
            methodPackage + "." + methodClass, usedTypeElement, nonPrimaryClassesToPrimaryClass);
      }
    }
    String methodWithoutAnySpace = methodName.replaceAll("\\s", "");
    if (this.targetMethodNames.contains(methodWithoutAnySpace)) {
      ResolvedMethodDeclaration resolvedMethod = method.resolve();
      updateUsedClassesForInterface(resolvedMethod);
      updateUsedClassWithQualifiedClassName(
          resolvedMethod.getPackageName() + "." + resolvedMethod.getClassName(),
          usedTypeElement,
          nonPrimaryClassesToPrimaryClass);

      // Process any annotations that may be present in generic parameter types,
      // like Collection<@KeyForBottom ? extends T> (check AnnoInGenericTargetTest)
      for (Parameter param : method.getParameters()) {
        Type paramType = param.getType();
  
        // Handle arrays of generics
        if (paramType.isArrayType()) {
          paramType = paramType.asArrayType().getElementType();
        }
  
        // Generics are only available with class/interface types
        if (paramType.isClassOrInterfaceType()) {
          Optional<NodeList<Type>> typeArguments =
              paramType.asClassOrInterfaceType().getTypeArguments();
  
          if (!typeArguments.isPresent()) {
            continue;
          }
  
          for (Type type : typeArguments.get()) {
            processAnnotations(type.getAnnotations());
          }
        }
      }
      
      processAnnotations(method.getAnnotations());
      insideTargetMember = true;
      targetMethods.add(resolvedMethod.getQualifiedSignature());
      // make sure that differences in spacing does not interfere with the result
      for (String unfound : unfoundMethods.keySet()) {
        if (unfound.replaceAll("\\s", "").equals(methodWithoutAnySpace)) {
          unfoundMethods.remove(unfound);
          break;
        }
      }
      Type returnType = method.getType();
      // JavaParser may misinterpret unresolved array types as reference types.
      // To ensure accuracy, we resolve the type before proceeding with the check.
      try {
        ResolvedType resolvedType = returnType.resolve();
        if (resolvedType instanceof ResolvedReferenceType) {
          updateUsedClassBasedOnType(resolvedType);
        }
      } catch (UnsupportedOperationException e) {
        // Occurs if the type is a type variable, so there is nothing to do:
        // the type variable must have been declared in one of the containing scopes,
        // and UnsolvedSymbolVisitor should already guarantee that the variable will
        // be included in one of the classes that Specimin outputs.
      } catch (UnsolvedSymbolException e) {
        throw new RuntimeException(
            "failed to solve the return type ("
                + returnType
                + ") of "
                + methodWithoutReturnAndAnnos,
            e);
      }
    } else {
      updateUnfoundMethods(methodName);
    }

    Visitable result = super.visit(method, p);
    insideTargetMember = oldInsideTargetMember;
    return result;
  }

  @Override
  public Visitable visit(Parameter para, Void p) {
    if (insideTargetMember) {
      Type type = para.getType();
      // an unknown type plays the role of a null object for lambda parameters that have no explicit
      // type declared. However, we also want to avoid trying to solve declared lambda params (it
      // will
      // fail, despite the fact that the code should be compilable).
      boolean isLambdaParam = type.isUnknownType() || isLambdaParam(para);
      if (type.isUnionType()) {
        resolveUnionType(type.asUnionType());
      } else if (!isLambdaParam) {
        // Parameter resolution (para.resolve()) does not work in catch clause.
        // However, resolution works on the type of the parameter.
        // Bug report: https://github.com/javaparser/javaparser/issues/4240
        ResolvedType paramType;
        if (para.getParentNode().isPresent() && para.getParentNode().get() instanceof CatchClause) {
          paramType = para.getType().resolve();
        } else {
          try {
            paramType = para.resolve().getType();
          } catch (UnsupportedOperationException e) {
            throw new RuntimeException("cannot solve: " + para, e);
          }
        }

        processAnnotations(para.getAnnotations());

        if (paramType.isReferenceType()) {
          String paraTypeFullName =
              paramType.asReferenceType().getTypeDeclaration().orElseThrow().getQualifiedName();
          updateUsedClassWithQualifiedClassName(
              paraTypeFullName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
          for (ResolvedType typeParameterValue :
              paramType.asReferenceType().typeParametersValues()) {
            String typeParameterValueName = typeParameterValue.describe();
            if (typeParameterValueName.contains("<")) {
              // removing the "<...>" part if there is any.
              typeParameterValueName =
                  typeParameterValueName.substring(0, typeParameterValueName.indexOf("<"));
            }
            updateUsedClassWithQualifiedClassName(
                typeParameterValueName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
          }
        }
      }
    }

    return super.visit(para, p);
  }

  /**
   * Returns true iff we can prove that the parameter is a lambda parameter. This method should only
   * be called on parameters that are not of unknown type (which are definitely lambda params).
   *
   * @param para a parameter
   * @return true iff para is a (typed) parameter in a lambda
   */
  private boolean isLambdaParam(Parameter para) {
    return para.getParentNode().orElseThrow() instanceof LambdaExpr;
  }

  @Override
  public Visitable visit(MethodReferenceExpr ref, Void p) {
    if (insideTargetMember) {
      ResolvedMethodDeclaration decl = ref.resolve();
      preserveMethodDecl(decl);
    }
    return super.visit(ref, p);
  }

  @Override
  public Visitable visit(MethodCallExpr call, Void p) {
    if (insideTargetMember) {
      ResolvedMethodDeclaration decl;
      try {
        decl = call.resolve();
      } catch (UnsupportedOperationException e) {
        // This case only occurs when a method is called on a lambda parameter.
        // JavaParser has a type variable for the lambda parameter, but it won't
        // have any constraints (JavaParser isn't very good at solving lambda parameter
        // types). The approach here preserves any method that might be the callee that's
        // in the input (based on the simple name of the method and its number of parameters).
        // TODO: this approach is both unsound and imprecise but works most of the time on
        // real examples. A better approach would be to either:
        // * update to a new version of JavaParser that _can_ solve lambda parameters
        // (we believe that newer JP versions are much improved), or
        // * add another javac pass after pruning that checks for this kind of error.
        resolvedYetStuckMethodCall.add(call.getNameAsString() + "@" + call.getArguments().size());
        return super.visit(call, p);
      } catch (RuntimeException e) {
        // Handle cases where a method call is resolved but its signature confuses JavaParser,
        // leading to a RuntimeException.
        // Note: this preservation is safe because we are not having an UnsolvedSymbolException.
        // Only unsolved symbols can make the output failed to compile.
        if (call.hasScope()) {
          Expression scope = call.getScope().orElseThrow();
          String scopeAsString = scope.toString();
          if (scopeAsString.equals("this") || scopeAsString.equals("super")) {
            // In the "super" case, it would be better to add the name of an
            // extended or implemented class/interface. However, there are two complications:
            // 1) we currently don't track the list of classes/interfaces that the current class
            // extends and/or implements in this visitor and 2) even if we did track that, there
            // is no way for us to know which of those classes/interfaces the method belongs to.
            // TODO: write a test for the "super" case and then figure out a better way to handle
            // it.
            resolvedYetStuckMethodCall.add(this.classFQName + "." + call.getNameAsString());
          } else {
            // Use the scope instead. There are two cases: the scope is an FQN (e.g., in
            // a call to a fully-qualified static method) or the scope is a simple name.
            // In the simple name case, append the current package to the front, since
            // if it had been imported we wouldn't be in this situation.
            if (UnsolvedSymbolVisitor.isAClassPath(scopeAsString)) {
              resolvedYetStuckMethodCall.add(scopeAsString + "." + call.getNameAsString());
              usedTypeElement.add(scopeAsString);
            } else {
              resolvedYetStuckMethodCall.add(
                  getCurrentPackage() + "." + scopeAsString + "." + call.getNameAsString());
              usedTypeElement.add(getCurrentPackage() + "." + scopeAsString);
            }
          }
        } else {
          resolvedYetStuckMethodCall.add(this.classFQName + "." + call.getNameAsString());
        }
        return super.visit(call, p);
      }
      preserveMethodDecl(decl);
      // Special case for lambdas to preserve artificial functional
      // interfaces.
      for (int i = 0; i < call.getArguments().size(); ++i) {
        Expression arg = call.getArgument(i);
        if (arg.isLambdaExpr()) {
          updateUsedClassBasedOnType(decl.getParam(i).getType());
        }
      }
    }
    return super.visit(call, p);
  }

  /**
   * Helper method for preserving a used method. This code is called for both method call
   * expressions and method refs.
   *
   * @param decl a resolved method declaration to be preserved
   */
  private void preserveMethodDecl(ResolvedMethodDeclaration decl) {
    usedMembers.add(decl.getQualifiedSignature());
    updateUsedClassWithQualifiedClassName(
        decl.getPackageName() + "." + decl.getClassName(),
        usedTypeElement,
        nonPrimaryClassesToPrimaryClass);
    try {
      ResolvedType methodReturnType = decl.getReturnType();
      if (methodReturnType instanceof ResolvedReferenceType) {
        updateUsedClassBasedOnType(methodReturnType);
      }
    }
    // There could be two cases here:
    // 1) The return type is a completely generic type.
    // 2) UnsolvedSymbolVisitor has missed some unsolved symbols.
    catch (UnsolvedSymbolException e) {
      return;
    }

    for (int i = 0; i < decl.getNumberOfParams(); ++i) {
      // Why is there no getParams() method??
      ResolvedParameterDeclaration p = decl.getParam(i);
      ResolvedType pType = p.getType();
      updateUsedClassBasedOnType(pType);
    }
  }

  /**
   * Gets the package name of the current class.
   *
   * @return the current package name
   */
  private String getCurrentPackage() {
    return currentPackage;
  }

  @Override
  public Visitable visit(ClassOrInterfaceType type, Void p) {
    if (!insideTargetMember) {
      return super.visit(type, p);
    }
    try {
      ResolvedReferenceType typeResolved =
          JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(type);
      updateUsedClassBasedOnType(typeResolved);
      processAnnotations(type.getAnnotations());
    }
    // if the type has a fully-qualified form, JavaParser also consider other components rather than
    // the class name as ClassOrInterfaceType. For example, if the type is org.A.B, then JavaParser
    // will also consider org and org.A as ClassOrInterfaceType.
    // if type is a type variable, we will get an UnsupportedOperation Exception.
    catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      return super.visit(type, p);
    }
    return super.visit(type, p);
  }

  @Override
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    if (insideTargetMember) {
      try {
        ResolvedConstructorDeclaration resolved = newExpr.resolve();
        usedMembers.add(resolved.getQualifiedSignature());
        updateUsedClassWithQualifiedClassName(
            resolved.getPackageName() + "." + resolved.getClassName(),
            usedTypeElement,
            nonPrimaryClassesToPrimaryClass);
        for (int i = 0; i < resolved.getNumberOfParams(); ++i) {
          // Why is there no getParams() method??
          ResolvedParameterDeclaration param = resolved.getParam(i);
          ResolvedType pType = param.getType();
          updateUsedClassBasedOnType(pType);
        }
      } catch (UnsolvedSymbolException e) {
        throw new RuntimeException("trying to resolve : " + newExpr, e);
      }
    }
    return super.visit(newExpr, p);
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt expr, Void p) {
    if (insideTargetMember) {
      ResolvedConstructorDeclaration resolved = expr.resolve();
      usedMembers.add(resolved.getQualifiedSignature());
      updateUsedClassWithQualifiedClassName(
          resolved.getPackageName() + "." + resolved.getClassName(),
          usedTypeElement,
          nonPrimaryClassesToPrimaryClass);
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(EnumConstantDeclaration enumConstantDeclaration, Void p) {
    Node parentNode = enumConstantDeclaration.getParentNode().orElseThrow();

    if (parentNode instanceof EnumDeclaration) {
      if (usedTypeElement.contains(
          ((EnumDeclaration) parentNode)
              .asEnumDeclaration()
              .getFullyQualifiedName()
              .orElseThrow())) {
        boolean oldInsideTargetMember = insideTargetMember;
        // used enum constant are not strictly target methods, but we need to make sure the symbols
        // inside them are preserved.
        insideTargetMember = true;
        Visitable result = super.visit(enumConstantDeclaration, p);
        insideTargetMember = oldInsideTargetMember;

        processAnnotations(enumConstantDeclaration.getAnnotations());
        return result;
      }
    }
    return super.visit(enumConstantDeclaration, p);
  }

  @Override
  public Visitable visit(FieldAccessExpr expr, Void p) {
    if (insideTargetMember) {
      String fullNameOfClass;
      if (updateUsedClassAndMemberForEnumConstant(expr)) {
        return super.visit(expr, p);
      }
      try {
        // while the name of the method is declaringType(), it actually returns the class where the
        // field is declared
        fullNameOfClass = expr.resolve().asField().declaringType().getQualifiedName();
        usedMembers.add(fullNameOfClass + "#" + expr.getName().asString());
        updateUsedClassWithQualifiedClassName(
            fullNameOfClass, usedTypeElement, nonPrimaryClassesToPrimaryClass);
        ResolvedType exprResolvedType = expr.resolve().getType();
        updateUsedClassBasedOnType(exprResolvedType);
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        // when the type is a primitive array, we will have an UnsupportedOperationException
        if (e instanceof UnsupportedOperationException) {
          Expression scope = expr.getScope();
          if (scope.isNameExpr()) {
            updateUsedElementWithPotentialFieldNameExpr(scope.asNameExpr());
          }
          // If the scope is not a name expression, then it must be "this" (handled elsewhere),
          // "super" (handled directly below), or another field access expression (handled by
          // the visitor), so there's nothing to do.
        }
        // if a field is accessed in the form of a fully-qualified path, such as
        // org.example.A.b, then other components in the path apart from the class name and field
        // name, such as org and org.example, will also be considered as FieldAccessExpr.
      }
    }
    Expression caller = expr.getScope();
    if (caller instanceof SuperExpr) {
      ResolvedType callerResolvedType = caller.calculateResolvedType();
      updateUsedClassBasedOnType(callerResolvedType);
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(NameExpr expr, Void p) {
    if (insideTargetMember) {
      Optional<Node> parentNode = expr.getParentNode();
      if (parentNode.isEmpty() || !(parentNode.get() instanceof FieldAccessExpr)) {
        updateUsedElementWithPotentialFieldNameExpr(expr);
      }
    }
    return super.visit(expr, p);
  }

  /**
   * Updates the list of used classes based on a resolved method declaration. If the input method
   * originates from an interface, that interface will be added to the list of used classes. The
   * determination of whether a method belongs to an interface is based on three criteria: method
   * name, method return type, and the number of parameters.
   *
   * @param method The resolved method declaration to be used for updating the list.
   */
  public void updateUsedClassesForInterface(ResolvedMethodDeclaration method) {
    for (ResolvedMethodDeclaration interfaceMethod : methodDeclarationToInterfaceType.keySet()) {
      if (method.getName().equals(interfaceMethod.getName())) {
        try {
          if (method
              .getReturnType()
              .describe()
              .equals(interfaceMethod.getReturnType().describe())) {
            if (method.getNumberOfParams() == interfaceMethod.getNumberOfParams()) {
              ResolvedReferenceType resolvedInterface =
                  JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(
                      methodDeclarationToInterfaceType.get(interfaceMethod));
              updateUsedClassWithQualifiedClassName(
                  resolvedInterface.getQualifiedName(),
                  usedTypeElement,
                  nonPrimaryClassesToPrimaryClass);
              usedMembers.add(interfaceMethod.getQualifiedSignature());
            }
          }
        } catch (UnsolvedSymbolException e) {
          // only potentially-used members will have their symbols solved.
          continue;
        }
      }
    }
  }

  /**
   * Given a method declaration, this method return the declaration of that method without the
   * return type and any possible annotation.
   *
   * @param methodDeclaration the method declaration to be used as input
   * @return methodDeclaration without the return type and any possible annotation.
   */
  public static String removeMethodReturnTypeAndAnnotations(String methodDeclaration) {
    String methodDeclarationWithoutParen =
        methodDeclaration.substring(0, methodDeclaration.indexOf("("));
    List<String> methodParts = Splitter.onPattern(" ").splitToList(methodDeclarationWithoutParen);
    String methodName = methodParts.get(methodParts.size() - 1);
    String methodReturnType = methodDeclaration.substring(0, methodDeclaration.indexOf(methodName));
    String methodWithoutReturnType = methodDeclaration.replace(methodReturnType, "");
    methodParts = Splitter.onPattern(" ").splitToList(methodWithoutReturnType);
    String filteredMethodDeclaration =
        methodParts.stream()
            .filter(part -> !part.startsWith("@"))
            .map(part -> part.indexOf('@') == -1 ? part : part.substring(0, part.indexOf('@')))
            .collect(Collectors.joining(" "));
    // sometimes an extra space may occur if an annotation right after a < was removed
    return filteredMethodDeclaration.replace("< ", "<");
  }

  /**
   * Resolve annotations one by one and adds the in the usedClass set.
   *
   * @param annotations The annotations to resolve
   */
  public void processAnnotations(NodeList<AnnotationExpr> annotations) {
    for (AnnotationExpr anno : annotations) {
      String qualifiedName = anno.resolve().getQualifiedName();
      updateUsedClassWithQualifiedClassName(
          qualifiedName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
    }
  }

  /**
   * Resolves unionType parameters one by one and adds them in the usedClass set.
   *
   * @param type unionType parameter
   */
  private void resolveUnionType(UnionType type) {
    for (ReferenceType param : type.getElements()) {
      ResolvedType paramType = param.resolve();
      updateUsedClassBasedOnType(paramType);
    }
  }

  /**
   * Given a FieldAccessExpr, this method updates the sets of used classes and members if this field
   * is actually an enum constant.
   *
   * @param fieldAccessExpr a potential enum constant.
   * @return true if the updating process was successful, false otherwise.
   */
  private boolean updateUsedClassAndMemberForEnumConstant(FieldAccessExpr fieldAccessExpr) {
    ResolvedValueDeclaration resolved;
    try {
      resolved = fieldAccessExpr.resolve();
    }
    // if the a field is accessed in the form of a fully-qualified path, such as
    // org.example.A.b, then other components in the path apart from the class name and field
    // name, such as org and org.example, will also be considered as FieldAccessExpr.
    catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      return false;
    }
    if (!resolved.isEnumConstant()) {
      return false;
    }
    String classFullName = resolved.asEnumConstant().getType().describe();
    updateUsedClassWithQualifiedClassName(
        classFullName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
    usedMembers.add(classFullName + "." + fieldAccessExpr.getNameAsString());
    return true;
  }

  /**
   * Given a NameExpr instance, this method will update the used elements, classes and members if
   * that NameExpr is a field.
   *
   * @param expr a field access expression inside target methods
   */
  public void updateUsedElementWithPotentialFieldNameExpr(NameExpr expr) {
    ResolvedValueDeclaration exprDecl;
    try {
      exprDecl = expr.resolve();
    } catch (UnsolvedSymbolException e) {
      // if expr is the name of a class in a static call, we can't resolve its value.
      return;
    }
    if (exprDecl instanceof ResolvedFieldDeclaration) {
      // while the name of the method is declaringType(), it actually returns the class where the
      // field is declared
      String classFullName = exprDecl.asField().declaringType().getQualifiedName();
      updateUsedClassWithQualifiedClassName(
          classFullName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
      usedMembers.add(classFullName + "#" + expr.getNameAsString());
      updateUsedClassBasedOnType(exprDecl.getType());
    } else if (exprDecl instanceof ResolvedEnumConstantDeclaration) {
      String enumFullName = exprDecl.asEnumConstant().getType().describe();
      updateUsedClassWithQualifiedClassName(
          enumFullName, usedTypeElement, nonPrimaryClassesToPrimaryClass);
      // "." and not "#" because enum constants are not fields
      usedMembers.add(enumFullName + "." + expr.getNameAsString());
      updateUsedClassBasedOnType(exprDecl.getType());
    }
  }

  /**
   * Updates the list of used type elements with the given qualified type name and its corresponding
   * primary type and enclosing type. This includes cases such as classes not sharing the same name
   * as their Java files or nested classes.
   *
   * @param qualifiedClassName The qualified class name to be included in the list of used type
   *     elements.
   * @param usedTypeElement The set of used type elements to be updated.
   * @param nonPrimaryClassesToPrimaryClass Map connecting non-primary classes to their
   *     corresponding primary classes.
   */
  public static void updateUsedClassWithQualifiedClassName(
      String qualifiedClassName,
      Set<String> usedTypeElement,
      Map<String, String> nonPrimaryClassesToPrimaryClass) {
    // in case of type variables
    if (!qualifiedClassName.contains(".")) {
      return;
    }
    // strip type variables, if they're present
    if (qualifiedClassName.contains("<")) {
      qualifiedClassName = qualifiedClassName.substring(0, qualifiedClassName.indexOf("<"));
    }
    usedTypeElement.add(qualifiedClassName);
    // in case this class is not a primary class.
    if (nonPrimaryClassesToPrimaryClass.containsKey(qualifiedClassName)) {
      updateUsedClassWithQualifiedClassName(
          nonPrimaryClassesToPrimaryClass.get(qualifiedClassName),
          usedTypeElement,
          nonPrimaryClassesToPrimaryClass);
    }

    String potentialOuterClass =
        qualifiedClassName.substring(0, qualifiedClassName.lastIndexOf("."));
    if (UnsolvedSymbolVisitor.isAClassPath(potentialOuterClass)) {
      updateUsedClassWithQualifiedClassName(
          potentialOuterClass, usedTypeElement, nonPrimaryClassesToPrimaryClass);
    }
  }

  /**
   * Updates the list of used classes based on the resolved type of a used element, where a element
   * can be a method, a field, a variable, or a parameter. Also updates the set of used classes
   * based on component types, wildcard bounds, etc., as needed: any type that is used in the type
   * will be included.
   *
   * @param type The resolved type of the used element.
   */
  public void updateUsedClassBasedOnType(ResolvedType type) {
    if (type.isTypeVariable()) {
      // From JLS 4.4: A type variable is introduced by the declaration of a type parameter of a
      // generic class, interface, method, or constructor
      ResolvedTypeParameterDeclaration asTypeParameter = type.asTypeParameter();
      for (ResolvedTypeParameterDeclaration.Bound bound : asTypeParameter.getBounds()) {
        updateUsedClassWithQualifiedClassName(
            bound.getType().describe(), usedTypeElement, nonPrimaryClassesToPrimaryClass);
      }
      return;
    } else if (type.isArray()) {
      ResolvedType componentType = type.asArrayType().getComponentType();
      updateUsedClassBasedOnType(componentType);
      return;
    }
    updateUsedClassWithQualifiedClassName(
        type.describe(), usedTypeElement, nonPrimaryClassesToPrimaryClass);
    if (!type.isReferenceType()) {
      return;
    }
    ResolvedReferenceType typeAsReference = type.asReferenceType();
    List<ResolvedType> typeParameters = typeAsReference.typeParametersValues();
    for (ResolvedType typePara : typeParameters) {
      if (typePara.isPrimitive() || typePara.isTypeVariable()) {
        // Nothing to do, since these are already in-scope.
        continue;
      }
      if (typePara.isWildcard()) {
        ResolvedWildcard asWildcard = typePara.asWildcard();
        // Recurse into the bound, if one exists.
        if (asWildcard.isBounded()) {
          updateUsedClassBasedOnType(asWildcard.getBoundedType());
        }
        continue;
      }
      updateUsedClassWithQualifiedClassName(
          typePara.asReferenceType().getQualifiedName(),
          usedTypeElement,
          nonPrimaryClassesToPrimaryClass);
    }
  }
}
