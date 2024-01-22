package org.checkerframework.specimin;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import java.util.Iterator;
import java.util.Set;

/**
 * This visitor removes every member in the compilation unit that is not a member of its {@link
 * #methodsToLeaveUnchanged} set or {@link #membersToEmpty} set. It also deletes the bodies of all
 * methods and replaces them with "throw new Error();" or remove the initializers of fields
 * (minimized if the field is final) within the {@link #membersToEmpty} set.
 */
public class PrunerVisitor extends ModifierVisitor<Void> {

  /**
   * The methods that should NOT be touched by this pruner. The strings representing the method are
   * those returned by ResolvedMethodDeclaration#getQualifiedSignature.
   */
  private Set<String> methodsToLeaveUnchanged;

  /**
   * The members, fields and methods, to be pruned. For methods, the bodies are removed. For fields,
   * the initializers are removed, or minimized in case the field is final. The strings representing
   * the method are those returned by ResolvedMethodDeclaration#getQualifiedSignature. The strings
   * representing the field are returned by ResolvedTypeDeclaration#getQualifiedName.
   */
  private Set<String> membersToEmpty;

  /**
   * This is the set of classes used by the target methods. We use this set to determine if we
   * should keep or delete an import statement. The strings representing the classes are in
   * the @FullyQualifiedName form.
   */
  private Set<String> classesUsedByTargetMethods;

  /**
   * This boolean tracks whether the element currently being visited is inside a target method. It
   * is set by {@link #visit(MethodDeclaration, Void)}.
   */
  private boolean insideTargetMethod = false;

  /**
   * Creates the pruner. All members this pruner encounters other than those in its input sets will
   * be removed entirely. For methods in both arguments, the Strings should be in the format
   * produced by ResolvedMethodDeclaration#getQualifiedSignature. For fields in {@link
   * #membersToEmpty}, the Strings should be in the format produced by
   * ResolvedTypeDeclaration#getQualifiedName.
   *
   * @param methodsToKeep the set of methods whose bodies should be kept intact (usually the target
   *     methods for specimin)
   * @param membersToEmpty the set of members that this pruner will empty
   * @param classesUsedByTargetMethods the classes used by target methods
   */
  public PrunerVisitor(
      Set<String> methodsToKeep,
      Set<String> membersToEmpty,
      Set<String> classesUsedByTargetMethods) {
    this.methodsToLeaveUnchanged = methodsToKeep;
    this.membersToEmpty = membersToEmpty;
    this.classesUsedByTargetMethods = classesUsedByTargetMethods;
  }

  @Override
  public Node visit(ImportDeclaration decl, Void p) {
    String classFullName = decl.getNameAsString();
    if (decl.isStatic()) {
      classFullName = classFullName.substring(0, classFullName.lastIndexOf("."));
    }
    if (classesUsedByTargetMethods.contains(classFullName)) {
      return super.visit(decl, p);
    }
    decl.remove();
    return decl;
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
    if (!classesUsedByTargetMethods.contains(decl.resolve().getQualifiedName())) {
      decl.remove();
      return decl;
    }
    return super.visit(decl, p);
  }

  @Override
  public Visitable visit(InitializerDeclaration decl, Void p) {
    decl.remove();
    return decl;
  }

  @Override
  public Visitable visit(MethodDeclaration methodDecl, Void p) {
    try {
      // resolved() will only check if the return type is solvable
      // getQualifiedSignature() will also check if the parameters are solvable
      methodDecl.resolve().getQualifiedSignature();
    } catch (UnsolvedSymbolException e) {
      // The current class is employed by the target methods, although not all of its members are
      // utilized. It's not surprising for unused members to remain unresolved.
      methodDecl.remove();
      return methodDecl;
    }
    ResolvedMethodDeclaration resolved = methodDecl.resolve();
    if (methodsToLeaveUnchanged.contains(resolved.getQualifiedSignature())) {
      insideTargetMethod = true;
      Visitable result = super.visit(methodDecl, p);
      insideTargetMethod = false;
      return result;
    } else if (membersToEmpty.contains(resolved.getQualifiedSignature())) {
      methodDecl.setBody(StaticJavaParser.parseBlock("{ throw new Error(); }"));
      return methodDecl;
    } else {
      // if insideTargetMethod is true, this current method declaration belongs to an anonnymous
      // class inside the target method.
      if (!insideTargetMethod) {
        methodDecl.remove();
      }
      return methodDecl;
    }
  }

  @Override
  public Visitable visit(ConstructorDeclaration constructorDecl, Void p) {
    try {
      // resolved() will only check if the return type is solvable
      // getQualifiedSignature() will also check if the parameters are solvable
      constructorDecl.resolve().getQualifiedSignature();
    } catch (UnsolvedSymbolException e) {
      // The current class is employed by the target methods, although not all of its members are
      // utilized. It's not surprising for unused members to remain unresolved.
      constructorDecl.remove();
      return constructorDecl;
    }
    ResolvedConstructorDeclaration resolved = constructorDecl.resolve();
    if (methodsToLeaveUnchanged.contains(resolved.getQualifiedSignature())) {
      return super.visit(constructorDecl, p);
    }

    if (membersToEmpty.contains(resolved.getQualifiedSignature())) {
      constructorDecl.setBody(StaticJavaParser.parseBlock("{ throw new Error(); }"));
      return constructorDecl;
    }

    constructorDecl.remove();
    return constructorDecl;
  }

  @Override
  public Visitable visit(FieldDeclaration fieldDecl, Void p) {
    try {
      fieldDecl.resolve();
    } catch (UnsolvedSymbolException e) {
      // The current class is employed by the target methods, although not all of its members are
      // utilized. It's not surprising for unused members to remain unresolved.
      fieldDecl.remove();
      return fieldDecl;
    }
    String classFullName = fieldDecl.resolve().declaringType().getQualifiedName();
    boolean isFinal = fieldDecl.isFinal();
    Iterator<VariableDeclarator> iterator = fieldDecl.getVariables().iterator();
    while (iterator.hasNext()) {
      VariableDeclarator varDecl = iterator.next();
      String varFullName = classFullName + "#" + varDecl.getNameAsString();

      if (membersToEmpty.contains(varFullName)) {
        varDecl.removeInitializer();
        if (isFinal) {
          varDecl.setInitializer(getBasicInitializer(varDecl.getType()));
        }
      } else {
        iterator.remove();
      }
    }

    return super.visit(fieldDecl, p);
  }

  /**
   * Creates a basic initializer expression for a specified field type. The way the initial value is
   * chosen is based on the document of the Java Language:
   * https://docs.oracle.com/javase/specs/jls/se7/html/jls-4.html#jls-4.12.5
   *
   * @param fieldType The type for which to generate the basic initializer.
   * @return An Expression representing the basic initializer for the given field type.
   */
  private Expression getBasicInitializer(Type fieldType) {
    if (fieldType.isPrimitiveType()) {
      PrimitiveType.Primitive primitiveType = ((PrimitiveType) fieldType).getType();
      switch (primitiveType) {
        case BOOLEAN:
          return new BooleanLiteralExpr(false);
        case INT:
          return new IntegerLiteralExpr("0");
        case LONG:
          return new LongLiteralExpr("0L");
        case FLOAT:
          return new DoubleLiteralExpr("0.0f");
        case DOUBLE:
          return new DoubleLiteralExpr("0.0");
        case BYTE:
          return new IntegerLiteralExpr("0");
        case SHORT:
          return new IntegerLiteralExpr("0");
        case CHAR:
          return new CharLiteralExpr("'\u0000'");
        default:
          throw new RuntimeException("Unexpected primitive type: " + fieldType);
      }
    }
    return new NullLiteralExpr();
  }
}
