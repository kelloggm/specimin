package org.checkerframework.specimin;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.signature.qual.FullyQualifiedName;

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
   * This boolean tracks whether the element currently being visited is inside an interface
   * annotated as @FunctionalInterface. This annotation is added to allow lambdas in target methods
   * to be passed to other methods, so the methods in such interfaces need to be preserved.
   */
  private boolean insideFunctionalInterface = false;

  /**
   * JavaParser is not perfect. Sometimes it can't solve resolved method calls if they have
   * complicated type variables. We keep track of these stuck method calls and preserve them anyway.
   */
  private final Set<String> resolvedYetStuckMethodCall;

  /** This map connects a class and its unresolved interface. */
  private Map<String, String> classAndUnresolvedInterface;

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
   * @param resolvedYetStuckMethodCall set of methods that are resolved yet can not be solved by
   *     JavaParser
   * @param classAndUnresolvedInterface connects a class to its corresponding unresolved interface
   */
  public PrunerVisitor(
      Set<String> methodsToKeep,
      Set<String> membersToEmpty,
      Set<String> classesUsedByTargetMethods,
      Set<String> resolvedYetStuckMethodCall,
      Map<String, String> classAndUnresolvedInterface) {
    this.methodsToLeaveUnchanged = methodsToKeep;
    this.membersToEmpty = membersToEmpty;
    this.classesUsedByTargetMethods = classesUsedByTargetMethods;
    this.classAndUnresolvedInterface = classAndUnresolvedInterface;
    Set<String> toRemove = new HashSet<>();
    for (String classUsedByTargetMethods : classesUsedByTargetMethods) {
      if (classUsedByTargetMethods.contains("<")) {
        toRemove.add(classUsedByTargetMethods);
      }
    }
    for (String s : toRemove) {
      classesUsedByTargetMethods.remove(s);
      String withoutAngleBrackets = s.substring(0, s.indexOf("<"));
      classesUsedByTargetMethods.add(withoutAngleBrackets);
    }
    this.resolvedYetStuckMethodCall = resolvedYetStuckMethodCall;
  }

  @Override
  public Node visit(ImportDeclaration decl, Void p) {
    String classFullName = decl.getNameAsString();
    if (decl.isAsterisk()) {
      // This looks weird, but in testing I found that iff decl represents a wildcard,
      // the result of getNameAsString is actually the package name. This renaming is just to
      // make the code less confusing.
      String importedPackage = classFullName;
      boolean isUsedAtLeastOnce = false;
      for (String usedClassFQN : classesUsedByTargetMethods) {
        if (usedClassFQN.startsWith(importedPackage)) {
          isUsedAtLeastOnce = true;
        }
      }
      if (!isUsedAtLeastOnce) {
        decl.remove();
      }
      return decl;
    }
    if (decl.isStatic()) {
      // if it's a static import, classFullName will actually be a method name
      if (isUsedMethod(classFullName)) {
        return super.visit(decl, p);
      }
    } else if (classesUsedByTargetMethods.contains(classFullName)) {
      return super.visit(decl, p);
    }
    decl.remove();
    return decl;
  }

  /**
   * Checks if the given static import of a method or field is a used method or field
   *
   * @param staticImport a fully-qualified static name of a method or field, dot-separated
   * @return true if a method with this name will be preserved
   */
  private boolean isUsedMethod(String staticImport) {
    for (String methodSignature : methodsToLeaveUnchanged) {
      if (methodSignature.startsWith(staticImport)) {
        return true;
      }
    }
    int lastDotIndex = staticImport.lastIndexOf('.');
    StringBuilder asFieldNameBuilder = new StringBuilder(staticImport);
    asFieldNameBuilder.setCharAt(lastDotIndex, '#');
    String asFieldName = asFieldNameBuilder.toString();
    for (String member : membersToEmpty) {
      if (member.startsWith(staticImport)) {
        return true;
      }
      if (member.equals(asFieldName)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
    boolean oldInsideFunctionalInterface = insideFunctionalInterface;
    for (AnnotationExpr anno : decl.getAnnotations()) {
      if (anno.getNameAsString().equals("FunctionalInterface")) {
        insideFunctionalInterface = true;
      }
    }
    decl = minimizeTypeParameters(decl);
    String classQualifiedName = decl.resolve().getQualifiedName();
    if (!classesUsedByTargetMethods.contains(classQualifiedName)) {
      decl.remove();
      return decl;
    }
    if (!decl.isInterface()) {
      NodeList<ClassOrInterfaceType> implementedInterfaces = decl.getImplementedTypes();
      Iterator<ClassOrInterfaceType> iterator = implementedInterfaces.iterator();
      while (iterator.hasNext()) {
        ClassOrInterfaceType interfaceType = iterator.next();
        try {
          String typeFullName = interfaceType.resolve().getQualifiedName();
          if (!classesUsedByTargetMethods.contains(typeFullName)) {
            iterator.remove();
          }
          // all unresolvable interfaces that need to be removed belong to the Java package.
          if (!typeFullName.startsWith("java.")) {
            continue;
          }
          for (String classNeedInterfaceRemoved : classAndUnresolvedInterface.keySet()) {
            // since classNeedInterfaceRemoved can be in the form of a simple name
            if (classQualifiedName.endsWith(classNeedInterfaceRemoved)) {
              if (classAndUnresolvedInterface
                  .get(classNeedInterfaceRemoved)
                  .equals(interfaceType.getNameAsString())) {
                // This code assumes that the likelihood of two different classes with the same
                // simple name implementing the same interface is low.
                iterator.remove();
              }
            }
          }
        } catch (UnsolvedSymbolException e) {
          iterator.remove();
        }
      }
      decl.setImplementedTypes(implementedInterfaces);
    }
    Visitable result = super.visit(decl, p);
    insideFunctionalInterface = oldInsideFunctionalInterface;
    return result;
  }

  @Override
  public Visitable visit(InitializerDeclaration decl, Void p) {
    decl.remove();
    return decl;
  }

  @Override
  public Visitable visit(EnumConstantDeclaration enumConstantDeclaration, Void p) {
    ResolvedEnumConstantDeclaration resolved;
    try {
      resolved = enumConstantDeclaration.resolve();
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      JavaParserUtil.removeNode(enumConstantDeclaration);
      return enumConstantDeclaration;
    }
    if (!membersToEmpty.contains(
        resolved.getType().describe() + "." + enumConstantDeclaration.getNameAsString())) {
      JavaParserUtil.removeNode(enumConstantDeclaration);
    }
    return enumConstantDeclaration;
  }

  @Override
  public Visitable visit(MethodDeclaration methodDecl, Void p) {
    if (insideFunctionalInterface) {
      return methodDecl;
    }
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
      boolean oldInsideTargetMethod = insideTargetMethod;
      insideTargetMethod = true;
      Visitable result = super.visit(methodDecl, p);
      insideTargetMethod = oldInsideTargetMethod;
      return result;
    } else if (membersToEmpty.contains(resolved.getQualifiedSignature())
        || isAResolvedYetStuckMethod(methodDecl)) {
      boolean isMethodInsideInterface = isInsideInterface(methodDecl);
      // do nothing if methodDecl is just a method signature in a class.
      if (methodDecl.getBody().isPresent() || isMethodInsideInterface) {
        methodDecl.setBody(StaticJavaParser.parseBlock("{ throw new Error(); }"));
        if (isMethodInsideInterface) {
          methodDecl.setDefault(true);
        }
      }
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
    String qualifiedSignature;
    try {
      // resolved() will only check if the return type is solvable
      // getQualifiedSignature() will also check if the parameters are solvable
      qualifiedSignature = constructorDecl.resolve().getQualifiedSignature();
    } catch (RuntimeException e) {
      // The current class is employed by the target methods, although not all of its members are
      // utilized. It's not surprising for unused members to remain unresolved.
      // If this constructor is from the parent of the current class, and it is not resolved, we
      // will get a RuntimeException, otherwise just a UnsolvedSymbolException.
      constructorDecl.remove();
      return constructorDecl;
    }

    // TODO: we should be cleverer about whether to preserve the constructors of
    // enums, but right now we don't remove any enum constants in related classes, so
    // we need to preserve all constructors to retain compilability.

    if (methodsToLeaveUnchanged.contains(qualifiedSignature)) {
      return super.visit(constructorDecl, p);
    } else if (membersToEmpty.contains(qualifiedSignature) || isInEnum(constructorDecl)) {
      constructorDecl.setBody(StaticJavaParser.parseBlock("{ throw new Error(); }"));
      return constructorDecl;
    } else {
      constructorDecl.remove();
      return constructorDecl;
    }
  }

  @Override
  public Visitable visit(FieldDeclaration fieldDecl, Void p) {
    if (insideTargetMethod) {
      return super.visit(fieldDecl, p);
    }

    boolean isFinal = fieldDecl.isFinal();
    String classFullName = getEnclosingClassName(fieldDecl);
    Iterator<VariableDeclarator> iterator = fieldDecl.getVariables().iterator();
    while (iterator.hasNext()) {
      VariableDeclarator declarator = iterator.next();
      try {
        declarator.resolve();
      } catch (UnsolvedSymbolException e) {
        // The current class is employed by the target methods, although not all of its members are
        // utilized. It's not surprising for unused members to remain unresolved.
        declarator.remove();
        continue;
      }
      String varFullName = classFullName + "#" + declarator.getNameAsString();

      if (membersToEmpty.contains(varFullName)) {
        declarator.removeInitializer();
        if (isFinal) {
          declarator.setInitializer(getBasicInitializer(declarator.getType()));
        }
      } else {
        iterator.remove();
      }
    }

    return super.visit(fieldDecl, p);
  }

  /**
   * Check if this method is one of the method calls used by target methods that are resolved yet
   * can not be solved by JavaParser.
   *
   * @param method a method
   * @return true if the above statement is true.
   */
  private boolean isAResolvedYetStuckMethod(MethodDeclaration method) {
    ResolvedMethodDeclaration decl = method.resolve();
    String methodQualifiedName = decl.getQualifiedSignature();
    String methodSimpleName = method.getNameAsString();
    int numberOfParams = decl.getNumberOfParams();
    boolean isVarArgs = numberOfParams == 0 ? false : decl.getLastParam().isVariadic();
    for (String stuckMethodCall : resolvedYetStuckMethodCall) {
      if (stuckMethodCall.contains("@")) {
        // The stuck method call contains an @ iff it is in the stuck method call
        // list because we couldn't determine its qualified signature from the context
        // in which it was called (e.g., a method called on a lambda parameter).
        // The format is the name of the method followed by an @ followed by the
        // number of arguments at the call site. Preserve anything that matches.
        String stuckMethodName = stuckMethodCall.substring(0, stuckMethodCall.indexOf('@'));
        int stuckMethodNumberOfParams =
            Integer.parseInt(stuckMethodCall.substring(stuckMethodCall.indexOf('@') + 1));
        if (methodSimpleName.equals(stuckMethodName)
            && ((!isVarArgs && numberOfParams == stuckMethodNumberOfParams)
                || (isVarArgs && numberOfParams <= stuckMethodNumberOfParams))) {
          return true;
        }
      } else if (methodQualifiedName.startsWith(stuckMethodCall)) {
        return true;
      }
    }
    return false;
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
    } else {
      return new NullLiteralExpr();
    }
  }

  /**
   * Given the declaration of a class, this method returns the updated declaration with the unused
   * type bounds of the type parameters removed.
   *
   * @param decl the declaration of a class.
   * @return that declaration with unused type bounds of type parameters removed.
   */
  private ClassOrInterfaceDeclaration minimizeTypeParameters(ClassOrInterfaceDeclaration decl) {
    NodeList<TypeParameter> typeParameterList = decl.getTypeParameters();
    NodeList<TypeParameter> updatedTypeParameterList = new NodeList<>();
    for (TypeParameter typeParameter : typeParameterList) {
      typeParameter = typeParameter.setTypeBound(getUsedTypesOnly(typeParameter.getTypeBound()));
      updatedTypeParameterList.add(typeParameter);
    }
    return decl.setTypeParameters(updatedTypeParameterList);
  }

  /**
   * Given a NodeList of types, this method removes those type not used by target methods.
   *
   * @param inputList a NodeList of ClassOrInterfaceType instances.
   * @return the updated list with unused types removed.
   */
  private NodeList<ClassOrInterfaceType> getUsedTypesOnly(
      NodeList<ClassOrInterfaceType> inputList) {
    NodeList<ClassOrInterfaceType> usedTypeOnly = new NodeList<>();
    for (ClassOrInterfaceType type : inputList) {
      ResolvedType resolvedType;
      try {
        resolvedType = type.resolve();
      } catch (UnsolvedSymbolException e) {
        continue;
      }
      if (classesUsedByTargetMethods.contains(resolvedType.asReferenceType().getQualifiedName())) {
        usedTypeOnly.add(type);
      }
    }
    return usedTypeOnly;
  }

  /**
   * Searches the ancestors of the given node until it finds a class or interface node, and then
   * returns the fully-qualified name of that class or interface.
   *
   * <p>This method will fail if it is called on a node that is not contained in a class or
   * interface.
   *
   * @param node a node contained in a class or interface
   * @return the fully-qualified name of the inner-most containing class or interface
   */
  @SuppressWarnings("signature") // result is a fully-qualified name or else this throws
  public static @FullyQualifiedName String getEnclosingClassName(Node node) {
    Node parent = getEnclosingClassLike(node);
    if (parent instanceof ClassOrInterfaceDeclaration) {
      return ((ClassOrInterfaceDeclaration) parent).getFullyQualifiedName().orElseThrow();
    } else if (parent instanceof EnumDeclaration) {
      return ((EnumDeclaration) parent).getFullyQualifiedName().orElseThrow();
    } else {
      throw new RuntimeException("unexpected kind of node: " + parent.getClass());
    }
  }

  /**
   * Returns the innermost enclosing class-like element for the given node. A class-like element is
   * a class, interface, or enum (i.e., something that would be a {@link
   * javax.lang.model.element.TypeElement} in javac's internal model). This method will throw if no
   * such element exists.
   *
   * @param node a node that is contained in a class-like structure
   * @return the nearest enclosing class-like node
   */
  public static Node getEnclosingClassLike(Node node) {
    Node parent = node.getParentNode().orElseThrow();
    while (!(parent instanceof ClassOrInterfaceDeclaration || parent instanceof EnumDeclaration)) {
      parent = parent.getParentNode().orElseThrow();
    }
    return parent;
  }

  /**
   * Returns true iff the innermost enclosing class/interface is an enum.
   *
   * @param node any node
   * @return true if the enclosing class is an enum, false otherwise
   */
  public static boolean isInEnum(Node node) {
    Optional<Node> parent = node.getParentNode();
    while (parent.isPresent()) {
      Node actualParent = parent.get();
      if (actualParent instanceof EnumDeclaration) {
        return true;
      }
      parent = actualParent.getParentNode();
    }
    return false;
  }

  /**
   * Check if a node is inside an interface.
   *
   * @param node the node to be checked.
   * @return true if node is inside an interface.
   */
  private boolean isInsideInterface(Node node) {
    if (node.getParentNode().isEmpty()) {
      return false;
    }
    Node parentNode = node.getParentNode().get();
    if (parentNode instanceof ClassOrInterfaceDeclaration) {
      return ((ClassOrInterfaceDeclaration) parentNode).isInterface();
    }
    return isInsideInterface(parentNode);
  }
}
