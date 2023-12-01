package org.checkerframework.specimin;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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
   * A list of Java files containing the declarations of unsolved symbols used by the target
   * methods. The reason we have these kinds of files is that UnsolvedSymbolVisitor will only create
   * synthetic files for files specified in the --targetFiles argument. At this point, we only
   * include one case, which is the lacking of information about a method's return type causing that
   * method to be unsolved. For other types, we should have enough data to create synthetic files
   * for them at the point they are used (no need to look up their declarations).
   */
  private final Set<String> listOfUsedYetUnsolvedFile = new HashSet<>();

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
   * Get the list of Java files containing unsolved symbols used by target methods
   *
   * @return the value of listOfUsedYetUnsolvedFile
   */
  public Set<String> getListOfUsedYetUnsolvedFile() {
    return listOfUsedYetUnsolvedFile;
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
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
      insideTargetMethod = true;
      targetMethods.add(method.resolve().getQualifiedSignature());
      unfoundMethods.remove(methodName);
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
    // The substring here is to remove the method's return type. Return types cannot contain spaces.
    // TODO: test this with annotations
    String methodName =
        this.classFQName + "#" + methodDeclAsString.substring(methodDeclAsString.indexOf(' ') + 1);
    // this method belongs to an anonymous class inside the target method
    if (insideTargetMethod) {
      ObjectCreationExpr parentExpression = (ObjectCreationExpr) method.getParentNode().get();
      ResolvedConstructorDeclaration resolved = parentExpression.resolve();
      String methodPackage = resolved.getPackageName();
      String methodClass = resolved.getClassName();
      usedMembers.add(methodPackage + "." + methodClass + "." + method.getNameAsString() + "()");
      usedClass.add(methodPackage + "." + methodClass);
    }

    if (this.targetMethodNames.contains(methodName)) {
      insideTargetMethod = true;
      targetMethods.add(method.resolve().getQualifiedSignature());
      unfoundMethods.remove(methodName);
      Type returnType = method.getType();
      // JavaParser may misinterpret unresolved array types as reference types.
      // To ensure accuracy, we resolve the type before proceeding with the check.
      try {
        ResolvedType resolvedType = returnType.resolve();
        if (resolvedType instanceof ResolvedReferenceType) {
          usedClass.add(resolvedType.asReferenceType().getQualifiedName());
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
  public Visitable visit(Parameter para, Void p) {
    if (insideTargetMethod) {
      Type type = para.getType();
      if (type.isUnionType()) {
        resolveUnionType(type.asUnionType());
      } else {
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
          usedClass.add(paraTypeFullName);
          for (ResolvedType typeParameterValue :
              paramType.asReferenceType().typeParametersValues()) {
            String typeParameterValueName = typeParameterValue.describe();
            if (typeParameterValueName.contains("<")) {
              // removing the "<...>" part if there is any.
              typeParameterValueName =
                  typeParameterValueName.substring(0, typeParameterValueName.indexOf("<"));
            }
            usedClass.add(typeParameterValueName);
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
      // the full name of the class that contain this method
      String classFullName = call.resolve().getPackageName() + "." + call.resolve().getClassName();
      usedClass.add(classFullName);
      ResolvedType methodReturnType;
      try {
        methodReturnType = call.resolve().getReturnType();
      } catch (UnsolvedSymbolException e) {
        listOfUsedYetUnsolvedFile.add(converClassNameToDirectory(classFullName));
        return super.visit(call, p);
      }
      if (methodReturnType instanceof ResolvedReferenceType) {
        usedClass.add(methodReturnType.asReferenceType().getQualifiedName());
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
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    if (insideTargetMethod) {
      usedMembers.add(newExpr.resolve().getQualifiedSignature());
      usedClass.add(newExpr.resolve().getPackageName() + "." + newExpr.resolve().getClassName());
    }
    return super.visit(newExpr, p);
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt expr, Void p) {
    if (insideTargetMethod) {
      usedMembers.add(expr.resolve().getQualifiedSignature());
      usedClass.add(expr.resolve().getPackageName() + "." + expr.resolve().getClassName());
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
        ResolvedFieldDeclaration resolvedField = expr.resolve().asField();
        fullNameOfClass = resolvedField.declaringType().getQualifiedName();
        usedMembers.add(fullNameOfClass + "#" + expr.getName().asString());
        usedClass.add(fullNameOfClass);
        try {
          ResolvedType typeOfField = resolvedField.getType();
          usedClass.add(typeOfField.describe());
        } catch (UnsolvedSymbolException e) {
          listOfUsedYetUnsolvedFile.add(converClassNameToDirectory(fullNameOfClass));
        }
      } catch (UnsolvedSymbolException e) {
        // if the a field is accessed in the form of a fully-qualified path, such as
        // org.example.A.b, then other components in the path apart from the class name and field
        // name, such as org and org.example, will also be considered as FieldAccessExpr.
      }
    }
    Expression caller = expr.getScope();
    if (caller instanceof SuperExpr) {
      usedClass.add(caller.calculateResolvedType().describe());
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
   * Resolves unionType parameters one by one and adds them in the usedClass set.
   *
   * @param type unionType parameter
   */
  private void resolveUnionType(UnionType type) {
    for (ReferenceType param : type.getElements()) {
      ResolvedType paramType = param.resolve();
      String paraTypeFullName =
          paramType.asReferenceType().getTypeDeclaration().get().getQualifiedName();
      usedClass.add(paraTypeFullName);
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
      usedClass.add(classFullName);
      usedMembers.add(classFullName + "#" + expr.getNameAsString());
    }
  }

  /**
   * Given the fully qualified name of a class, this method returns the directory of the Java file
   * that contains the input class. The directory will be relative to the root directory of the
   * input class.
   *
   * @param className the fully qualified name of a class
   * @return the directory of the corresponding Java file
   */
  private String converClassNameToDirectory(String className) {
    String fileName = className.replace(".", "/");
    if (fileName.contains("$")) {
      // remove the inner class part
      fileName = fileName.substring(0, fileName.indexOf("$"));
    }
    return fileName + ".java";
  }
}
