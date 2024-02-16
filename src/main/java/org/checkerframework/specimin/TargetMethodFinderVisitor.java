package org.checkerframework.specimin;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
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
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.google.common.base.Splitter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The main visitor for Specimin's first phase, which locates the target method(s) and compiles
 * information on what specifications they use.
 */
public class TargetMethodFinderVisitor extends ModifierVisitor<Void> {
  /**
   * The names of the target methods. The format is
   * class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
   */
  private Set<String> targetMethodNames;

  /**
   * This boolean tracks whether the element currently being visited is inside a target method. It
   * is set by {@link #visit(MethodDeclaration, Void)}.
   */
  private boolean insideTargetMethod = false;

  /** The fully-qualified name of the class currently being visited. */
  private String classFQName = "";

  /**
   * The members (methods and fields) that were actually used by the targets, and therefore ought to
   * have their specifications (but not bodies) preserved. The Strings in the set are the
   * fully-qualified names, as returned by ResolvedMethodDeclaration#getQualifiedSignature for
   * methods and FieldAccessExpr#getName for fields.
   */
  private final Set<String> usedMembers = new HashSet<>();

  /**
   * Classes of the methods that were actually used by the targets. These classes will be included
   * in the input.
   */
  private Set<String> usedClass = new HashSet<>();

  /** Set of variables declared in this current class */
  private final Set<String> declaredNames = new HashSet<>();

  /**
   * The resolved target methods. The Strings in the set are the fully-qualified names, as returned
   * by ResolvedMethodDeclaration#getQualifiedSignature.
   */
  private final Set<String> targetMethods = new HashSet<>();

  /**
   * A local copy of the input list of methods. A method is removed from this copy when it is
   * located. If the visitor has been run on all source files and this list isn't empty, that
   * usually indicates an error.
   */
  private final List<String> unfoundMethods;

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
   * Create a new target method finding visitor.
   *
   * @param methodNames the names of the target methods, the format
   *     class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
   */
  public TargetMethodFinderVisitor(List<String> methodNames) {
    targetMethodNames = new HashSet<>();
    targetMethodNames.addAll(methodNames);
    unfoundMethods = new ArrayList<>(methodNames);
    importedClassToPackage = new HashMap<>();
  }

  /**
   * Returns the methods that so far this visitor has not located from its target list. Usually,
   * this should be checked after running the visitor to ensure that it is empty.
   *
   * @return the methods that so far this visitor has not located from its target list
   */
  public List<String> getUnfoundMethods() {
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
   * Get the classes of the methods that the target method uses. The Strings in the set are the
   * fully-qualified names.
   *
   * @return the used classes
   */
  public Set<String> getUsedClass() {
    return usedClass;
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
            interfaceType.resolve().asReferenceType().getAllMethods(), interfaceType);
      } catch (UnsolvedSymbolException e) {
        continue;
      }
    }

    if (decl.isNestedType()) {
      this.classFQName += "." + decl.getName().toString();
    } else {
      if (!this.classFQName.equals("")) {
        throw new UnsupportedOperationException(
            "Attempted to enter an unexpected kind of class: "
                + decl.getFullyQualifiedName()
                + " but already had a set classFQName: "
                + classFQName);
      }
      // Should always be present.
      this.classFQName = decl.getFullyQualifiedName().orElseThrow();
    }
    Visitable result = super.visit(decl, p);
    if (decl.isNestedType()) {
      this.classFQName = this.classFQName.substring(0, this.classFQName.lastIndexOf('.'));
    } else {
      this.classFQName = "";
    }
    return result;
  }

  @Override
  public Visitable visit(ConstructorDeclaration method, Void p) {
    String constructorMethodAsString = method.getDeclarationAsString(false, false, false);
    // the methodName will be something like this: "com.example.Car#Car()"
    String methodName = this.classFQName + "#" + constructorMethodAsString;
    if (this.targetMethodNames.contains(methodName)) {
      updateUsedClassWithQualifiedClassName(
          method.resolve().getPackageName() + "." + method.resolve().getClassName());
      insideTargetMethod = true;
      ResolvedConstructorDeclaration resolvedMethod = method.resolve();
      targetMethods.add(resolvedMethod.getQualifiedSignature());
      unfoundMethods.remove(methodName);
      usedClass.add(resolvedMethod.getPackageName() + "." + resolvedMethod.getClassName());
    }
    Visitable result = super.visit(method, p);
    insideTargetMethod = false;
    return result;
  }

  @Override
  public Visitable visit(VariableDeclarator node, Void arg) {
    declaredNames.add(node.getNameAsString());
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(MethodDeclaration method, Void p) {
    String methodDeclAsString = method.getDeclarationAsString(false, false, false);
    // TODO: test this with annotations
    String methodName = this.classFQName + "#" + removeMethodReturnType(methodDeclAsString);
    // this method belongs to an anonymous class inside the target method
    if (insideTargetMethod) {
      ObjectCreationExpr parentExpression = (ObjectCreationExpr) method.getParentNode().get();
      ResolvedConstructorDeclaration resolved = parentExpression.resolve();
      String methodPackage = resolved.getPackageName();
      String methodClass = resolved.getClassName();
      usedMembers.add(methodPackage + "." + methodClass + "." + method.getNameAsString() + "()");
      updateUsedClassWithQualifiedClassName(methodPackage + "." + methodClass);
    }

    if (this.targetMethodNames.contains(methodName)) {
      ResolvedMethodDeclaration resolvedMethod = method.resolve();
      updateUsedClassesForInterface(resolvedMethod);
      updateUsedClassWithQualifiedClassName(
          method.resolve().getPackageName() + "." + resolvedMethod.getClassName());
      insideTargetMethod = true;
      targetMethods.add(resolvedMethod.getQualifiedSignature());
      unfoundMethods.remove(methodName);
      usedClass.add(resolvedMethod.getPackageName() + "." + resolvedMethod.getClassName());
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
      }
    }
    Visitable result = super.visit(method, p);
    insideTargetMethod = false;
    return result;
  }

  @Override
  public Visitable visit(MarkerAnnotationExpr expr, Void p) {
    if (insideTargetMethod) {
      String annotationName = expr.getNameAsString();
      if (importedClassToPackage.containsKey(annotationName)) {
        usedClass.add(importedClassToPackage.get(annotationName) + "." + annotationName);
      }
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(NormalAnnotationExpr expr, Void p) {
    if (insideTargetMethod) {
      String annotationName = expr.getNameAsString();
      if (importedClassToPackage.containsKey(annotationName)) {
        usedClass.add(importedClassToPackage.get(annotationName) + "." + annotationName);
      }
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(SingleMemberAnnotationExpr expr, Void p) {
    if (insideTargetMethod) {
      String annotationName = expr.getNameAsString();
      if (importedClassToPackage.containsKey(annotationName)) {
        usedClass.add(importedClassToPackage.get(annotationName) + "." + annotationName);
      }
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(Parameter para, Void p) {
    if (insideTargetMethod) {
      Type type = para.getType();
      if (type.isUnionType()) {
        resolveUnionType(type.asUnionType());
      }
      // an unknown type plays the role of a null object for lambda parameters that have no explicit
      // type declared
      else if (!type.isUnknownType()) {
        // Parameter resolution (para.resolve()) does not work in catch clause.
        // However, resolution works on the type of the parameter.
        // Bug report: https://github.com/javaparser/javaparser/issues/4240
        ResolvedType paramType;
        if (para.getParentNode().isPresent() && para.getParentNode().get() instanceof CatchClause) {
          paramType = para.getType().resolve();
        } else {
          paramType = para.resolve().getType();
        }

        if (paramType.isReferenceType()) {
          String paraTypeFullName =
              paramType.asReferenceType().getTypeDeclaration().get().getQualifiedName();
          updateUsedClassWithQualifiedClassName(paraTypeFullName);
          for (ResolvedType typeParameterValue :
              paramType.asReferenceType().typeParametersValues()) {
            String typeParameterValueName = typeParameterValue.describe();
            if (typeParameterValueName.contains("<")) {
              // removing the "<...>" part if there is any.
              typeParameterValueName =
                  typeParameterValueName.substring(0, typeParameterValueName.indexOf("<"));
            }
            updateUsedClassWithQualifiedClassName(typeParameterValueName);
          }
        }
      }
    }
    return super.visit(para, p);
  }

  @Override
  public Visitable visit(MethodCallExpr call, Void p) {
    if (insideTargetMethod) {
      usedMembers.add(call.resolve().getQualifiedSignature());
      updateUsedClassWithQualifiedClassName(
          call.resolve().getPackageName() + "." + call.resolve().getClassName());
      ResolvedType methodReturnType = call.resolve().getReturnType();
      if (methodReturnType instanceof ResolvedReferenceType) {
        updateUsedClassBasedOnType(methodReturnType);
      }
      if (call.getScope().isPresent()) {
        Expression scope = call.getScope().get();
        // if the scope of a method call is a field, the type of that scope will be NameExpr.
        if (scope instanceof NameExpr) {
          NameExpr expression = call.getScope().get().asNameExpr();
          updateUsedElementWithPotentialFieldNameExpr(expression);
        }
      }
    }
    return super.visit(call, p);
  }

  @Override
  public Visitable visit(ClassOrInterfaceType type, Void p) {
    if (!insideTargetMethod) {
      return super.visit(type, p);
    }
    try {
      ResolvedType typeResolved = type.resolve();
      updateUsedClassBasedOnType(typeResolved);
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
    if (insideTargetMethod) {
      usedMembers.add(newExpr.resolve().getQualifiedSignature());
      updateUsedClassWithQualifiedClassName(
          newExpr.resolve().getPackageName() + "." + newExpr.resolve().getClassName());
    }
    return super.visit(newExpr, p);
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt expr, Void p) {
    if (insideTargetMethod) {
      usedMembers.add(expr.resolve().getQualifiedSignature());
      updateUsedClassWithQualifiedClassName(
          expr.resolve().getPackageName() + "." + expr.resolve().getClassName());
    }
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(FieldAccessExpr expr, Void p) {
    if (insideTargetMethod) {
      String fullNameOfClass;
      try {
        // while the name of the method is declaringType(), it actually returns the class where the
        // field is declared
        fullNameOfClass = expr.resolve().asField().declaringType().getQualifiedName();
        usedMembers.add(fullNameOfClass + "#" + expr.getName().asString());
        updateUsedClassWithQualifiedClassName(fullNameOfClass);
        ResolvedType exprResolvedType = expr.resolve().getType();
        updateUsedClassBasedOnType(exprResolvedType);
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        // when the type is a primitive array, we will have an UnsupportedOperationException
        if (e instanceof UnsupportedOperationException) {
          updateUsedElementWithPotentialFieldNameExpr(expr.getScope().asNameExpr());
        }
        // if the a field is accessed in the form of a fully-qualified path, such as
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
    if (insideTargetMethod) {
      Optional<Node> parentNode = expr.getParentNode();
      if (parentNode.isEmpty()
          || !(parentNode.get() instanceof MethodCallExpr
              || parentNode.get() instanceof FieldAccessExpr)) {
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
        String methodReturnType = method.getReturnType().describe();
        String interfaceMethodReturnType = interfaceMethod.getReturnType().describe();
        if (methodReturnType.equals(interfaceMethodReturnType)) {
          if (method.getNumberOfParams() == interfaceMethod.getNumberOfParams()) {
            usedClass.add(
                methodDeclarationToInterfaceType
                    .get(interfaceMethod)
                    .resolve()
                    .asReferenceType()
                    .getQualifiedName());
            usedMembers.add(interfaceMethod.getQualifiedSignature());
          }
        }
      }
    }
  }

  /**
   * Given a method declaration, this method return the declaration of that method without the
   * return type.
   *
   * @param methodDeclaration the method declaration to be used as input
   * @return methodDeclaration without the return type
   */
  public static String removeMethodReturnType(String methodDeclaration) {
    String methodDeclarationWithoutParen =
        methodDeclaration.substring(0, methodDeclaration.indexOf("("));
    List<String> methodParts = Splitter.onPattern(" ").splitToList(methodDeclarationWithoutParen);
    String methodName = methodParts.get(methodParts.size() - 1);
    String methodReturnType = methodDeclaration.substring(0, methodDeclaration.indexOf(methodName));
    return methodDeclaration.replace(methodReturnType, "");
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
      updateUsedClassWithQualifiedClassName(classFullName);
      usedMembers.add(classFullName + "#" + expr.getNameAsString());
      updateUsedClassBasedOnType(exprDecl.getType());
    }
  }

  /**
   * Updates the list of used classes with the given qualified class name and its corresponding
   * enclosing classes, if applicable (in the case of nested classes).
   *
   * @param qualifiedClassName The qualified class name to be included in the list of used classes.
   */
  public void updateUsedClassWithQualifiedClassName(String qualifiedClassName) {
    // in case of type variables
    if (!qualifiedClassName.contains(".")) {
      return;
    }
    usedClass.add(qualifiedClassName);
    String potentialOuterClass =
        qualifiedClassName.substring(0, qualifiedClassName.lastIndexOf("."));
    if (UnsolvedSymbolVisitor.isAClassPath(potentialOuterClass)) {
      updateUsedClassWithQualifiedClassName(potentialOuterClass);
    }
  }

  /**
   * Updates the list of used classes based on the resolved type of a used element, where a element
   * can be a method, a field, a variable, or a parameter.
   *
   * @param type The resolved type of the used element.
   */
  public void updateUsedClassBasedOnType(ResolvedType type) {
    updateUsedClassWithQualifiedClassName(type.describe());
    if (!type.isReferenceType()) {
      return;
    }
    ResolvedReferenceType typeAsReference = type.asReferenceType();
    List<ResolvedType> typeParameters = typeAsReference.typeParametersValues();
    for (ResolvedType typePara : typeParameters) {
      if (typePara.isPrimitive() || typePara.isTypeVariable() || typePara.isWildcard()) {
        continue;
      }
      usedClass.add(typePara.asReferenceType().getQualifiedName());
    }
  }
}
