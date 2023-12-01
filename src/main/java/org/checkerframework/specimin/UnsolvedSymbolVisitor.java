package org.checkerframework.specimin;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.google.common.base.Splitter;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.checker.signature.qual.ClassGetSimpleName;
import org.checkerframework.checker.signature.qual.DotSeparatedIdentifiers;
import org.checkerframework.checker.signature.qual.FullyQualifiedName;

/**
 * The visitor for the preliminary phase of Specimin. This visitor goes through the input files,
 * notices all the methods belonging to classes not in the source codes, and creates synthetic
 * versions of those classes and methods. This preliminary step helps to prevent
 * UnsolvedSymbolException errors for the next phases.
 */
public class UnsolvedSymbolVisitor extends ModifierVisitor<Void> {

  /**
   * This map associates class names with their respective superclasses. The keys in this map
   * represent the classes of the currently visited file. Due to the potential presence of inner
   * classes, there may be multiple pairs of class and superclass entries in this map. This map can
   * also be empty if there are no superclasses other than java.lang.Object involved in the
   * currently visited file.
   */
  private final Map<String, @ClassGetSimpleName String> classAndItsParent = new HashMap<>();

  /** The package of this class */
  private String currentPackage = "";

  /** The symbol table to keep track of local variables in the current input file */
  private final ArrayDeque<HashSet<String>> localVariables = new ArrayDeque<>();

  /** The symbol table for type variables. */
  private final ArrayDeque<Set<String>> typeVariables = new ArrayDeque<Set<String>>();

  /** The simple name of the class currently visited */
  private @ClassGetSimpleName String className = "";

  /**
   * This map will map the name of variables in the current class and its corresponding declaration
   */
  private final Map<String, String> variablesAndDeclaration = new HashMap<>();

  /**
   * Based on the method declarations in the current class, this map will map the name of the
   * methods with their corresponding return types
   */
  private final Map<String, @ClassGetSimpleName String> methodAndReturnType = new HashMap<>();

  /** List of classes not in the source codes */
  private final Set<UnsolvedClass> missingClass = new HashSet<>();

  /** The same as the root being used in SpeciminRunner */
  private final String rootDirectory;

  /**
   * This boolean tracks whether the element currently being visited is inside an object creation.
   * It is set by {@link #visit(ObjectCreationExpr, Void)}. This boolean helps UnsolvedSymbolVisitor
   * recognize anonymous class.
   */
  private boolean insideAnObjectCreation = false;

  /** This instance maps the name of a synthetic method with its synthetic class */
  private final Map<String, UnsolvedClass> syntheticMethodAndClass = new HashMap<>();

  /**
   * This is to check if the current synthetic files are enough to prevent UnsolvedSymbolException
   * or we still need more.
   */
  private boolean gotException;

  /**
   * The list of classes that have been created. We use this list to delete all the temporary
   * synthetic classes when Specimin finishes its run
   */
  private final Set<Path> createdClass = new HashSet<>();

  /** List of import statement from the current compilation unit that is being visited */
  private List<String> importStatement = new ArrayList<>();

  /** This map the classes in the compilation unit with the related package */
  private final Map<String, String> classAndPackageMap = new HashMap<>();

  /** This set has fully-qualified class names that come from jar files input */
  private final Set<@FullyQualifiedName String> classesFromJar = new HashSet<>();

  /**
   * This set has the fully-qualfied name of the synthetic return types created by this instance of
   * UnsolvedSymbolVisitor
   */
  private final Set<String> syntheticReturnTypes = new HashSet<>();

  /**
   * This set has all the name of synthetic types created by this visitor. These types represent the
   * type of fields in the parent class of the current class.
   */
  private final Set<String> syntheticTypes = new HashSet<>();

  /**
   * A mapping of field name to the name of the class currently being visited and its inner classes
   */
  private Map<String, @ClassGetSimpleName String> fieldNameToClassNameMap = new HashMap<>();

  /**
   * Create a new UnsolvedSymbolVisitor instance
   *
   * @param rootDirectory the root directory of the input files
   */
  public UnsolvedSymbolVisitor(String rootDirectory) {
    this.rootDirectory = rootDirectory;
    this.gotException = true;
  }

  /**
   * Set importStatement equals to the list of import statements from the current compilation unit.
   * Also update the classAndPackageMap based on this new list.
   *
   * @param listOfImports NodeList of import statements from the compilation unit
   */
  public void setImportStatement(NodeList<ImportDeclaration> listOfImports) {
    List<String> currentImportList = new ArrayList<>();
    for (ImportDeclaration importStatement : listOfImports) {
      String importAsString = importStatement.getNameAsString();
      currentImportList.add(importAsString);
    }
    this.importStatement = currentImportList;
    this.setclassAndPackageMap();
  }

  /**
   * This method sets the value of classesFromJar based on the known class of jar type solvers
   *
   * @param jarPaths a list of path of jar files
   */
  public void setClassesFromJar(List<String> jarPaths) {
    for (String path : jarPaths) {
      try {
        classesFromJar.addAll(new JarTypeSolver(path).getKnownClasses());
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    }
  }
  /**
   * This method sets the classAndPackageMap. This method is called in the method
   * setImportStatement, as classAndPackageMap and importStatements should always be in sync.
   */
  private void setclassAndPackageMap() {
    for (String importStatement : this.importStatement) {
      List<String> importParts = Splitter.on('.').splitToList(importStatement);
      if (importParts.size() > 0) {
        String className = importParts.get(importParts.size() - 1);
        String packageName = importStatement.replace("." + className, "");
        if (className.equals("*")) {
          throw new RuntimeException(
              "A wildcard import statement found. Please use explicit import" + " statements.");
        } else {
          this.classAndPackageMap.put(className, packageName);
        }
      }
    }
  }

  /**
   * This method sets up the value of fieldsAndItsClass by using the result obtained from
   * FieldDeclarationsVisitor
   *
   * @param fieldNameToClassNameMap the value of fieldsAndItsClass from FieldDeclarationsVisitor
   */
  public void setFieldNameToClassNameMap(
      Map<String, @ClassGetSimpleName String> fieldNameToClassNameMap) {
    this.fieldNameToClassNameMap = fieldNameToClassNameMap;
  }

  /**
   * Get the collection of superclasses. Due to the potential presence of inner classes, this method
   * returns a collection, as there can be multiple superclasses involved in a single file.
   *
   * @return the collection of superclasses
   */
  public Collection<@ClassGetSimpleName String> getSuperClass() {
    return classAndItsParent.values();
  }

  /**
   * Get the value of gotException
   *
   * @return gotException the value of gotException
   */
  public boolean gettingException() {
    return gotException;
  }

  /**
   * Get the classes that have been created by the current iteration of the visitor.
   *
   * @return createdClass the Set of Path of classes that have beenc created
   */
  public Set<Path> getCreatedClass() {
    return createdClass;
  }

  /** Set gotException. */
  public void setException(boolean gotException) {
    this.gotException = gotException;
  }

  @Override
  public Visitable visit(PackageDeclaration node, Void arg) {
    this.currentPackage = node.getNameAsString();
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration node, Void arg) {
    SimpleName nodeName = node.getName();
    className = nodeName.asString();
    if (node.getExtendedTypes().isNonEmpty()) {
      // note that since Specimin does not have access to the classpaths of the project, all the
      // unsolved methods related to inheritance will be placed in the parent class, even if there
      // is a grandparent class and so forth.
      SimpleName superClassSimpleName = node.getExtendedTypes().get(0).getName();
      classAndItsParent.put(className, superClassSimpleName.asString());
    }
    addTypeVariableScope(node.getTypeParameters());
    Visitable result = super.visit(node, arg);
    typeVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt node, Void arg) {
    try {
      // check if the symbol is solvable. If it is, then there's no need to create a synthetic file.
      node.resolve().getQualifiedSignature();
      return super.visit(node, arg);
    } catch (Exception e) {
      NodeList<Expression> arguments = node.getArguments();
      List<String> parametersList = new ArrayList<>();
      for (Expression parameter : arguments) {
        if (!canBeSolved(parameter)) {
          return super.visit(node, arg);
        }
        ResolvedType type = parameter.calculateResolvedType();
        if (type instanceof PrimitiveType) {
          parametersList.add(type.asPrimitive().name());
        } else if (type instanceof ReferenceType) {
          parametersList.add(type.asReferenceType().getQualifiedName());
        }
      }
      UnsolvedMethod constructorMethod =
          new UnsolvedMethod(getParentClass(className), "", parametersList);
      // if the parent class can not be found in the import statements, Specimin assumes it is in
      // the same package as the child class.
      UnsolvedClass superClass =
          new UnsolvedClass(
              getParentClass(className),
              classAndPackageMap.getOrDefault(getParentClass(className), currentPackage));
      superClass.addMethod(constructorMethod);
      updateMissingClass(superClass);
      return super.visit(node, arg);
    }
  }

  @Override
  public Visitable visit(ForStmt node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  @SuppressWarnings("nullness:override")
  public @Nullable Visitable visit(IfStmt n, Void arg) {
    HashSet<String> localVarInCon = new HashSet<>();
    localVariables.addFirst(localVarInCon);
    Expression condition = (Expression) n.getCondition().accept(this, arg);
    localVariables.removeFirst();
    localVarInCon = new HashSet<>();
    localVariables.addFirst(localVarInCon);
    Statement elseStmt = n.getElseStmt().map(s -> (Statement) s.accept(this, arg)).orElse(null);
    localVariables.removeFirst();
    localVarInCon = new HashSet<>();
    localVariables.addFirst(localVarInCon);
    Statement thenStmt = (Statement) n.getThenStmt().accept(this, arg);
    localVariables.removeFirst();
    if (condition == null || thenStmt == null) {
      return null;
    }
    n.setCondition(condition);
    n.setElseStmt(elseStmt);
    n.setThenStmt(thenStmt);
    return n;
  }

  @Override
  public Visitable visit(WhileStmt node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(SwitchExpr node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(SwitchEntry node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(TryStmt node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(CatchClause node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(BlockStmt node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, p);
    localVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(VariableDeclarator decl, Void p) {
    // This part is to update the symbol table.
    boolean isAField =
        !decl.getParentNode().isEmpty() && (decl.getParentNode().get() instanceof FieldDeclaration);
    if (!isAField) {
      HashSet<String> currentListOfLocals = localVariables.removeFirst();
      currentListOfLocals.add(decl.getNameAsString());
      localVariables.addFirst(currentListOfLocals);
    }

    // This part is to create synthetic class for the type of decl if needed.
    Type declType = decl.getType();
    try {
      declType.resolve();
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      String typeAsString = declType.asString();
      List<String> elements = Splitter.onPattern("\\.").splitToList(typeAsString);
      // There could be three cases here: a type variable, a fully-qualified class name, or a simple
      // class name.
      // This is the fully-qualified case.
      if (elements.size() > 1) {
        @SuppressWarnings("signature") // since this type is in a fully-qualfied form
        @FullyQualifiedName String qualifiedTypeName = typeAsString;
        updateMissingClass(getSimpleSyntheticClassFromFullyQualifiedName(qualifiedTypeName));
      } else if (isTypeVar(typeAsString)) {
        // Nothing to do in this case, but we need to skip creating an unsolved class.
      }
      /**
       * Handles the case where the type is a simple class name. Two sub-cases are considered: 1.
       * The class is included among the import statements. 2. The class is not included in the
       * import statements but is in the same directory as the input class. The first sub-case is
       * addressed by the visit method for ImportDeclaration.
       */
      else if (!classAndPackageMap.containsKey(typeAsString)) {
        @SuppressWarnings("signature") // since this is the simple name case
        @ClassGetSimpleName String className = typeAsString;
        String packageName = this.currentPackage;
        UnsolvedClass newClass = new UnsolvedClass(className, packageName);
        updateMissingClass(newClass);
      }
    }
    return super.visit(decl, p);
  }

  @Override
  public Visitable visit(NameExpr node, Void arg) {
    String name = node.getNameAsString();
    if (fieldNameToClassNameMap.containsKey(name)) {
      return super.visit(node, arg);
    }
    // This method explicitly handles NameExpr instances that represent fields of classes but are
    // not explicitly shown in the code. For example, if "number" is a field of a class, then
    // "return number;" is an expression that this method will address. If the NameExpr instance is
    // not a field of any class, or if it is a field of a class but is explicitly referenced, such
    // as "Math.number," we handle it in other visit methods.
    if (!canBeSolved(node)) {
      Optional<Node> parentNode = node.getParentNode();
      // we take care of MethodCallExpr and FieldAccessExpr cases in other visit methods
      if (parentNode.isEmpty()
          || !(parentNode.get() instanceof MethodCallExpr
              || parentNode.get() instanceof FieldAccessExpr)) {
        if (!isALocalVar(name)) {
          updateSyntheticClassForSuperCall(node);
        }
      }
    }
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(FieldDeclaration node, Void arg) {
    for (VariableDeclarator var : node.getVariables()) {
      String variableName = var.getNameAsString();
      String variableType = node.getElementType().asString();
      Optional<Expression> potentialValue = var.getInitializer();
      String variableDeclaration = variableType + " " + variableName;
      if (potentialValue.isPresent()) {
        String variableValue = potentialValue.get().toString();
        variableDeclaration += " = " + variableValue;
      } else {
        variableDeclaration =
            this.setInitialValueForVariableDeclaration(variableType, variableDeclaration);
      }
      variablesAndDeclaration.put(variableName, variableDeclaration);
    }
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(ConstructorDeclaration node, Void arg) {
    // TODO: Loi: do we need to do anything for the parameters, like we do in
    // visit(MethodDeclaration)?
    addTypeVariableScope(node.getTypeParameters());
    Visitable result = super.visit(node, arg);
    typeVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(MethodDeclaration node, Void arg) {
    // a MethodDeclaration instance will have parent node
    Node parentNode = node.getParentNode().get();
    Type nodeType = node.getType();

    // This scope logic must happen here, because later in this method there is a check for
    // whether the return type is a type variable, which must succeed if the type variable
    // was declared for this scope.
    addTypeVariableScope(node.getTypeParameters());

    // since this is a return type of a method, it is a dot-separated identifier
    @SuppressWarnings("signature")
    @DotSeparatedIdentifiers String nodeTypeAsString = nodeType.asString();
    @ClassGetSimpleName String nodeTypeSimpleForm = toSimpleName(nodeTypeAsString);
    if (!this.isTypeVar(nodeTypeSimpleForm)) {
      // Don't attempt to resolve a type variable, since we will inevitably fail.
      try {
        nodeType.resolve();
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        updateUnsolvedClassWithClassName(nodeTypeSimpleForm, false);
      }
    }

    if (!insideAnObjectCreation) {
      SimpleName classNodeSimpleName = ((ClassOrInterfaceDeclaration) parentNode).getName();
      className = classNodeSimpleName.asString();
      methodAndReturnType.put(node.getNameAsString(), nodeTypeSimpleForm);
    }
    // node is a method declaration inside an anonymous class
    else {
      try {
        // since this method declaration is inside an anonymous class, its parent will be an
        // ObjectCreationExpr
        ((ObjectCreationExpr) parentNode).resolve();
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        SimpleName classNodeSimpleName = ((ObjectCreationExpr) parentNode).getType().getName();
        String nameOfClass = classNodeSimpleName.asString();
        updateUnsolvedClassWithMethod(node, nameOfClass, toSimpleName(nodeTypeAsString));
      }
    }
    HashSet<String> currentLocalVariables = getParameterFromAMethodDeclaration(node);
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, arg);
    localVariables.removeFirst();
    typeVariables.removeFirst();
    return result;
  }

  @Override
  public Visitable visit(FieldAccessExpr node, Void p) {
    if (isASuperCall(node) && !canBeSolved(node)) {
      updateSyntheticClassForSuperCall(node);
    }
    return super.visit(node, p);
  }

  @Override
  public Visitable visit(MethodCallExpr method, Void p) {
    if (canBeSolved(method) && isFromAJarFile(method)) {
      updateClassesFromJarSourcesForMethodCall(method);
      return super.visit(method, p);
    }
    if (isASuperCall(method) && !canBeSolved(method)) {
      updateSyntheticClassForSuperCall(method);
      return super.visit(method, p);
    }
    // we will wait for the next run to solve this method call
    if (!canSolveParameters(method)) {
      return super.visit(method, p);
    }
    if (isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method)) {
      updateClassSetWithQualifiedStaticMethodCall(
          method.toString(), getArgumentsFromMethodCall(method));
    } else if (calledByAnIncompleteSyntheticClass(method)) {
      @ClassGetSimpleName String incompleteClassName = getSyntheticClass(method);
      updateUnsolvedClassWithMethod(method, incompleteClassName, "");
    } else if (unsolvedAndCalledByASimpleClassName(method)) {
      String methodFullyQualifiedCall = toFullyQualifiedCall(method);
      updateClassSetWithQualifiedStaticMethodCall(
          methodFullyQualifiedCall, getArgumentsFromMethodCall(method));
    }
    try {
      method.resolve();
    } catch (UnsolvedSymbolException e) {
      this.gotException = true;
    }
    return super.visit(method, p);
  }

  @Override
  public Visitable visit(ClassOrInterfaceType typeExpr, Void p) {
    // Workaround for a JavaParser bug: When a type is referenced using its fully-qualified name,
    // like
    // com.example.Dog dog, JavaParser considers its package components (com and com.example) as
    // types, too. This issue happens even when the source file of the Dog class is present in the
    // codebase.
    if (!isCapital(typeExpr.getName().asString())) {
      return super.visit(typeExpr, p);
    }
    if (!typeExpr.isReferenceType()) {
      return super.visit(typeExpr, p);
    }
    try {
      typeExpr.getElementType().resolve().describe();
      return super.visit(typeExpr, p);
    }
    /*
     * If the class file is not in the codebase yet, we got UnsolvedSymbolException.
     * If the class file is not in the codebase and used by an anonymous class, we got UnsupportedOperationException.
     * If the class file is in the codebase but the type variables are missing, we got IllegalArgumentException.
     */
    catch (UnsolvedSymbolException | UnsupportedOperationException | IllegalArgumentException e) {
      // This method only updates type variables for unsolved classes. Other problems causing a
      // class to be unsolved will be fixed by other methods.
      Optional<NodeList<Type>> typeArguments = typeExpr.getTypeArguments();
      UnsolvedClass classToUpdate;
      int numberOfArguments = 0;
      String typeRawName = typeExpr.getElementType().asString();
      if (typeArguments.isPresent()) {
        numberOfArguments = typeArguments.get().size();
        // without any type argument
        typeRawName = typeRawName.substring(0, typeRawName.indexOf("<"));
      }
      if (isTypeVar(typeRawName)) {
        // If the type name itself is an in-scope type variable, just return without attempting
        // to create a missing class.
        return super.visit(typeExpr, p);
      } else if (isAClassPath(typeRawName)) {
        String packageName = typeRawName.substring(0, typeRawName.lastIndexOf("."));
        @SuppressWarnings("signature") // since this is the last element of a class path
        @ClassGetSimpleName String className = typeRawName.substring(typeRawName.lastIndexOf(".") + 1);
        classToUpdate = new UnsolvedClass(className, packageName);
      } else {
        @SuppressWarnings("signature") // since it is not in a fully qualifed format
        @ClassGetSimpleName String className = typeRawName;
        String packageName = classAndPackageMap.getOrDefault(className, currentPackage);
        classToUpdate = new UnsolvedClass(className, packageName);
      }
      classToUpdate.setNumberOfTypeVariables(numberOfArguments);
      updateMissingClass(classToUpdate);
      gotException = true;
    }
    return super.visit(typeExpr, p);
  }

  @Override
  public Visitable visit(Parameter parameter, Void p) {
    try {
      if (parameter.getType() instanceof UnionType) {
        resolveUnionType(parameter);
      } else {
        if (parameter.getParentNode().isPresent()
            && parameter.getParentNode().get() instanceof CatchClause) {
          parameter.getType().resolve();
        } else {
          parameter.resolve();
        }
      }
      return super.visit(parameter, p);
    }
    // If the parameter originates from a Java built-in library, such as java.io or java.lang,
    // an UnsupportedOperationException will be thrown instead.
    catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      handleParameterResolveFailure(parameter);
    }
    gotException = true;
    return super.visit(parameter, p);
  }

  @Override
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    SimpleName typeName = newExpr.getType().getName();
    String type = typeName.asString();
    if (canBeSolved(newExpr)) {
      if (isFromAJarFile(newExpr)) {
        updateClassesFromJarSourcesForObjectCreation(newExpr);
      }
      insideAnObjectCreation = true;
      super.visit(newExpr, p);
      insideAnObjectCreation = false;
      return newExpr;
    }
    this.gotException = true;
    try {
      List<String> argumentsCreation = getArgumentsFromObjectCreation(newExpr);
      UnsolvedMethod creationMethod = new UnsolvedMethod("", type, argumentsCreation);
      updateUnsolvedClassWithClassName(type, false, creationMethod);
    } catch (Exception q) {
      // can not solve the parameters for this object creation in this current run
    }
    insideAnObjectCreation = true;
    super.visit(newExpr, p);
    insideAnObjectCreation = false;
    return newExpr;
  }

  /**
   * @param parameter parameter from visitor method which is unsolvable.
   */
  private void handleParameterResolveFailure(@NonNull Parameter parameter) {
    String parameterInString = parameter.toString();
    if (isAClassPath(parameterInString)) {
      // parameterInString needs to be a fully-qualified name. As this parameter has a form of
      // class path, we can say that it is a fully-qualified name
      @SuppressWarnings("signature")
      UnsolvedClass newClass = getSimpleSyntheticClassFromFullyQualifiedName(parameterInString);
      updateMissingClass(newClass);
    } else {
      // since it is unsolved, it could not be a primitive type
      @ClassGetSimpleName String className = parameter.getType().asClassOrInterfaceType().getName().asString();
      if (parameter.getParentNode().isPresent()
          && parameter.getParentNode().get() instanceof CatchClause) {
        updateUnsolvedClassWithClassName(className, true);
      } else {
        updateUnsolvedClassWithClassName(className, false);
      }
    }
  }

  /**
   * Given the unionType parameter, this method will try resolving each element separately. If any
   * of the element is unsolvable, an unsolved class instance will be created to generate synthetic
   * class for the element.
   *
   * @param parameter unionType parameter from visitor class
   */
  private void resolveUnionType(@NonNull Parameter parameter) {
    for (var param : parameter.getType().asUnionType().getElements()) {
      try {
        param.resolve();
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        handleParameterResolveFailure(parameter);
      }
    }
  }

  /**
   * Given the variable type and the basic declaration of that variable (such as "int x", "boolean
   * y", "Car redTruck",...), this methods will add an initial value to that declaration of the
   * variable. The way the initial value is chosen is based on the document of the Java Language:
   * https://docs.oracle.com/javase/specs/jls/se7/html/jls-4.html#jls-4.12.5
   *
   * @param variableType the type of the variable
   * @param variableDeclaration the basic declaration of that variable
   * @return the declaration of the variable with an initial value
   */
  public static String setInitialValueForVariableDeclaration(
      String variableType, String variableDeclaration) {
    if (variableType.equals("byte")) {
      return variableDeclaration + " = (byte)0";
    } else if (variableType.equals("short")) {
      return variableDeclaration + " = (short)0";
    } else if (variableType.equals("int")) {
      return variableDeclaration + " = 0";
    } else if (variableType.equals("long")) {
      return variableDeclaration + " = 0L";
    } else if (variableType.equals("float")) {
      return variableDeclaration + " = 0.0f";
    } else if (variableType.equals("double")) {
      return variableDeclaration + " = 0.0d";
    } else if (variableType.equals("char")) {
      return variableDeclaration + " = '\\u0000'";
    } else if (variableType.equals("boolean")) {
      return variableDeclaration + " = false";
    } else {
      return variableDeclaration + " = null";
    }
  }

  /**
   * Given a class name that can either be fully-qualified or simple, this method will convert that
   * class name to a simple name.
   *
   * @param className the class name to be converted
   * @return the simple form of that class name
   */
  // We can have certainty that this method is true as the last element of a class name is the
  // simple form of that name
  @SuppressWarnings("signature")
  public static @ClassGetSimpleName String toSimpleName(@DotSeparatedIdentifiers String className) {
    List<String> elements = Splitter.onPattern("[.]").splitToList(className);
    if (elements.size() < 2) {
      return className;
    }
    return elements.get(elements.size() - 1);
  }

  /**
   * This method will add a new method declaration to a synthetic class based on the unsolved method
   * call or method declaration in the original input. User can choose the desired return type for
   * the added method. The desired return type can be an empty string, and in that case, Specimin
   * will create another synthetic class to be the return type of that method.
   *
   * @param method the method call or method declaration in the original input
   * @param className the name of the synthetic class
   * @param desiredReturnType the desired return type for this method
   */
  public void updateUnsolvedClassWithMethod(
      Node method,
      @ClassGetSimpleName String className,
      @ClassGetSimpleName String desiredReturnType) {
    String methodName = "";
    List<String> listOfParameters = new ArrayList<>();
    if (method instanceof MethodCallExpr) {
      methodName = ((MethodCallExpr) method).getNameAsString();
      listOfParameters = getArgumentsFromMethodCall(((MethodCallExpr) method));
    }
    // method is a MethodDeclaration
    else {
      methodName = ((MethodDeclaration) method).getNameAsString();
      for (Parameter para : ((MethodDeclaration) method).getParameters()) {
        listOfParameters.add(para.getNameAsString());
      }
    }
    String returnType = "";
    if (desiredReturnType.equals("")) {
      returnType = returnNameForMethod(methodName);
    } else {
      returnType = desiredReturnType;
    }
    UnsolvedMethod thisMethod = new UnsolvedMethod(methodName, returnType, listOfParameters);
    UnsolvedClass missingClass = updateUnsolvedClassWithClassName(className, false, thisMethod);
    syntheticMethodAndClass.put(methodName, missingClass);

    // if the return type is not specified, a synthetic return type will be created. This part of
    // codes creates the corresponding class for that synthetic return type
    if (desiredReturnType.equals("")) {
      @SuppressWarnings(
          "signature") // returnType is a @ClassGetSimpleName, so combining it with the package will
      // give us the fully-qualified name
      @FullyQualifiedName String packageName = missingClass.getPackageName() + "." + returnType;
      syntheticReturnTypes.add(packageName);
      UnsolvedClass returnTypeForThisMethod =
          new UnsolvedClass(returnType, missingClass.getPackageName());
      this.updateMissingClass(returnTypeForThisMethod);
      classAndPackageMap.put(
          returnTypeForThisMethod.getClassName(), returnTypeForThisMethod.getPackageName());
    }
  }

  /**
   * Checks if the given expression is solvable because the class file containing its symbol is
   * found in one of the jar files provided via the {@code --jarPath} option.
   *
   * @param expr The expression to be checked for solvability.
   * @return true iff the expression is solvable because its class file was found in one of the jar
   *     files.
   */
  public boolean isFromAJarFile(Expression expr) {
    String className;
    if (expr instanceof MethodCallExpr) {
      className =
          ((MethodCallExpr) expr).resolve().getPackageName()
              + "."
              + ((MethodCallExpr) expr).resolve().getClassName();
    } else if (expr instanceof ObjectCreationExpr) {
      String shortName = ((ObjectCreationExpr) expr).getTypeAsString();
      String packageName = classAndPackageMap.get(shortName);
      className = packageName + "." + shortName;
    } else {
      throw new RuntimeException("Unexpected call: " + expr + ". Contact developers!");
    }
    return classesFromJar.contains(className);
  }

  /**
   * This method updates a synthetic file based on a solvable expression. The input expression is
   * solvable because its data is in the jar files that Specimin taks as input.
   *
   * @param expr the expression to be used
   */
  public void updateClassesFromJarSourcesForMethodCall(MethodCallExpr expr) {
    if (!isFromAJarFile(expr)) {
      throw new RuntimeException(
          "Check with isFromAJarFile first before using updateClassesFromJarSources");
    }
    String methodName = expr.getNameAsString();
    ResolvedMethodDeclaration methodSolved = expr.resolve();
    @SuppressWarnings(
        "signature") // this is not a precise assumption, as getClassName() will return a
    // @FullyQualifiedName if the class is not of primitive type. However, this is
    // favorable, since we don't have to write any additional import statements.
    @ClassGetSimpleName String className = methodSolved.getClassName();
    String packageName = methodSolved.getPackageName();
    @SuppressWarnings(
        "signature") // this is not a precise assumption, as getReturnType().describe() will return
    // a @FullyQualifiedName if the class is not of primitive type. However, this
    // is favorable, since we don't have to write any additional import statements.
    @ClassGetSimpleName String returnType = methodSolved.getReturnType().describe();
    List<String> argumentsList = getArgumentsFromMethodCall(expr);
    UnsolvedClass missingClass = new UnsolvedClass(className, packageName);
    UnsolvedMethod thisMethod = new UnsolvedMethod(methodName, returnType, argumentsList);
    missingClass.addMethod(thisMethod);
    syntheticMethodAndClass.put(methodName, missingClass);
    this.updateMissingClass(missingClass);
  }

  /**
   * Given the simple name of an unsolved class, this method will create an UnsolvedClass instance
   * to represent that class and update the list of missing class with that UnsolvedClass instance.
   *
   * @param nameOfClass the name of an unsolved class
   * @param unsolvedMethods unsolved methods to add to the class before updating this visitor's set
   *     missing classes (optional, may be omitted)
   * @param isExceptionType if the class is of exceptionType
   * @return the newly-created UnsolvedClass method, for further processing. This output may be
   *     ignored.
   */
  public UnsolvedClass updateUnsolvedClassWithClassName(
      @ClassGetSimpleName String nameOfClass,
      boolean isExceptionType,
      UnsolvedMethod... unsolvedMethods) {
    // if the name of the class is not present among import statements, we assume that this unsolved
    // class is in the same directory as the current class
    String packageName = classAndPackageMap.getOrDefault(nameOfClass, currentPackage);
    UnsolvedClass result = new UnsolvedClass(nameOfClass, packageName, isExceptionType);
    for (UnsolvedMethod unsolvedMethod : unsolvedMethods) {
      result.addMethod(unsolvedMethod);
    }
    updateMissingClass(result);
    return result;
  }

  /**
   * This method updates a synthetic file based on a solvable expression. The input expression is
   * solvable because its data is in the jar files that Specimin taks as input.
   *
   * @param expr the expression to be used
   */
  public void updateClassesFromJarSourcesForObjectCreation(ObjectCreationExpr expr) {
    if (!isFromAJarFile(expr)) {
      throw new RuntimeException(
          "Check with isFromAJarFile first before using updateClassesFromJarSources");
    }
    String objectName = expr.getType().getName().asString();
    ResolvedReferenceTypeDeclaration objectSolved = expr.resolve().declaringType();
    @SuppressWarnings(
        "signature") // this is not a precise assumption, as getClassName() will return a
    // @FullyQualifiedName if the class is not of primitive type. However, this is
    // favorable, since we don't have to write any additional import statements.
    @ClassGetSimpleName String className = objectSolved.getClassName();
    String packageName = objectSolved.getPackageName();
    List<String> argumentsList = getArgumentsFromObjectCreation(expr);
    UnsolvedClass missingClass = new UnsolvedClass(className, packageName);
    UnsolvedMethod thisMethod = new UnsolvedMethod(objectName, "", argumentsList);
    missingClass.addMethod(thisMethod);
    this.updateMissingClass(missingClass);
  }

  /**
   * This method checks if an expression is called by the super keyword. For example, super.visit()
   * is such an expression.
   *
   * @param node the expression to be checked
   * @return true if method is a super call
   */
  public static boolean isASuperCall(Expression node) {
    if (node instanceof MethodCallExpr) {
      Optional<Expression> caller = node.asMethodCallExpr().getScope();
      if (caller.isEmpty()) {
        return false;
      }
      return caller.get().isSuperExpr();
    } else if (node instanceof FieldAccessExpr) {
      Expression caller = node.asFieldAccessExpr().getScope();
      return caller.isSuperExpr();
    } else if (node instanceof NameExpr) {
      // an unsolved name expression implies that it is declared in the parent class
      return !canBeSolved(node);
    } else {
      throw new RuntimeException("Unforeseen expression: " + node);
    }
  }

  /**
   * Given a method declaration, this method will return the set of parameters of that method
   * declaration.
   *
   * @param decl the method declaration
   * @return the set of parameters of decl
   */
  public HashSet<String> getParameterFromAMethodDeclaration(MethodDeclaration decl) {
    HashSet<String> setOfParameters = new HashSet<>();
    for (Parameter parameter : decl.getParameters()) {
      setOfParameters.add(parameter.getName().asString());
    }
    return setOfParameters;
  }

  /**
   * For a super call, this method will update the corresponding synthetic class
   *
   * @param expr the super call expression to be taken as input
   */
  public void updateSyntheticClassForSuperCall(Expression expr) {
    if (!isASuperCall(expr)) {
      throw new RuntimeException(
          "Check if isASuperCall returns true before calling updateSyntheticClassForSuperCall");
    }
    if (expr instanceof MethodCallExpr) {
      updateUnsolvedClassWithMethod(
          expr.asMethodCallExpr(),
          getParentClass(className),
          methodAndReturnType.getOrDefault(expr.asMethodCallExpr().getNameAsString(), ""));
    } else if (expr instanceof FieldAccessExpr) {
      String nameAsString = expr.asFieldAccessExpr().getNameAsString();
      updateUnsolvedClassWithFields(
          nameAsString,
          getParentClass(className),
          classAndPackageMap.getOrDefault(getParentClass(className), this.currentPackage));
    } else if (expr instanceof NameExpr) {
      String nameAsString = expr.asNameExpr().getNameAsString();
      updateUnsolvedClassWithFields(
          nameAsString,
          getParentClass(className),
          classAndPackageMap.getOrDefault(getParentClass(className), this.currentPackage));
    } else {
      throw new RuntimeException("Unexpected expression: " + expr);
    }
  }

  /**
   * This method will add a new field declaration to a synthetic class. This method is intended to
   * be used for unsolved superclass. The declaration of the field in the superclass will be the
   * same as the declaration in the child class since Specimin does not have access to much
   * information. If the field is not found in the child class, Specimin will create a synthetic
   * class to be the type of that field.
   *
   * @param var the field to be added
   * @param className the name of the synthetic class
   * @param packageName the package of the synthetic class
   */
  public void updateUnsolvedClassWithFields(
      String var, @ClassGetSimpleName String className, String packageName) {
    UnsolvedClass relatedClass = new UnsolvedClass(className, packageName);
    if (variablesAndDeclaration.containsKey(var)) {
      String variableExpression = variablesAndDeclaration.get(var);
      relatedClass.addFields(variableExpression);
      updateMissingClass(relatedClass);
    } else {
      // since it is just simple string combination, it is a simple name
      @SuppressWarnings("signature")
      @ClassGetSimpleName String variableType = "SyntheticTypeFor" + toCapital(var);
      UnsolvedClass varType = new UnsolvedClass(variableType, packageName);
      syntheticTypes.add(variableType);
      relatedClass.addFields(
          setInitialValueForVariableDeclaration(variableType, variableType + " " + var));
      updateMissingClass(relatedClass);
      updateMissingClass(varType);
    }
  }

  /**
   * This method checks if a variable is local.
   *
   * @param variableName the name of the variable
   * @return true if that variable is local
   */
  public boolean isALocalVar(String variableName) {
    for (HashSet<String> varSet : localVariables) {
      // for anonymous classes, it is assumed that any matching local variable either belongs to the
      // class itself or is a final variable in the enclosing scope.
      if (varSet.contains(variableName)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Is the given type name actually an in-scope type variable?
   *
   * @param typeName a simple name of a type, as written in a source file. The type name might be an
   *     in-scope type variable.
   * @return true iff there is a type variable in scope with this name. Returning false guarantees
   *     that there is no such type variable, but not that the input is a valid type.
   */
  private boolean isTypeVar(String typeName) {
    for (Set<String> scope : typeVariables) {
      if (scope.contains(typeName)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Adds a scope with the given list of type parameters. Each pair to this method must be paired
   * with a call to typeVariables.removeFirst().
   *
   * @param typeParameters a list of type parameters
   */
  private void addTypeVariableScope(List<TypeParameter> typeParameters) {
    Set<String> typeVariableScope = new HashSet<>();
    for (TypeParameter t : typeParameters) {
      typeVariableScope.add(t.getName().asString());
    }
    typeVariables.addFirst(typeVariableScope);
  }

  /**
   * This method checks if the current run of UnsolvedSymbolVisitor can solve the parameters' types
   * of a method call
   *
   * @param method the method call to be checked
   * @return true if UnsolvedSymbolVisitor can solve the types of parameters of method
   */
  public static boolean canSolveParameters(MethodCallExpr method) {
    NodeList<Expression> paraList = method.getArguments();
    if (paraList.isEmpty()) {
      return true;
    }
    for (Expression parameter : paraList) {
      if (!canBeSolved(parameter)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Given a method call, this method returns the list of types of the parameters of that method
   *
   * @param method the method to be analyzed
   * @return the types of parameters of method
   */
  public static List<String> getArgumentsFromMethodCall(MethodCallExpr method) {
    List<String> parametersList = new ArrayList<>();
    NodeList<Expression> paraList = method.getArguments();
    for (Expression parameter : paraList) {
      ResolvedType type = parameter.calculateResolvedType();
      // for reference type, we need the fully-qualified name to avoid having to add additional
      // import statements.
      if (type.isReferenceType()) {
        parametersList.add(((ResolvedReferenceType) type).getQualifiedName());
      } else if (type.isPrimitive()) {
        parametersList.add(type.describe());
      }
    }
    return parametersList;
  }

  /**
   * Given a new object creation, this method returns the list of types of the parameters of that
   * call
   *
   * @param creationExpr the object creation call
   * @return the types of parameters of the object creation method
   */
  public static List<String> getArgumentsFromObjectCreation(ObjectCreationExpr creationExpr) {
    List<String> parametersList = new ArrayList<>();
    NodeList<Expression> paraList = creationExpr.getArguments();
    for (Expression parameter : paraList) {
      ResolvedType type = parameter.calculateResolvedType();
      if (type.isReferenceType()) {
        parametersList.add(((ResolvedReferenceType) type).getQualifiedName());
      } else if (type.isPrimitive()) {
        parametersList.add(type.describe());
      }
    }
    return parametersList;
  }

  /**
   * As the name suggests, this method takes a MethodCallExpr instance as the input and checks if
   * the method in that expression is called by an unsolved symbol.
   *
   * @param method the method call to be analyzed
   * @return true if the method involved is called by an unsolved symbol
   */
  public static boolean calledByAnUnsolvedSymbol(MethodCallExpr method) {
    Optional<Expression> caller = method.getScope();
    if (!caller.isPresent()) {
      return false;
    }
    Expression callerExpression = caller.get();
    return !canBeSolved(callerExpression);
  }

  /**
   * This methods check if an Expression instance can be solved by SymbolSolver of JavaParser. If
   * the Expression instance can be solved, there is no need to create any synthetic method or class
   * for it.
   *
   * @param expr the expression to be checked
   * @return true if the expression can be solved
   */
  public static boolean canBeSolved(Expression expr) {
    try {
      expr.calculateResolvedType();
      return true;
    } catch (Exception e) {
      return false;
    }
  }

  /**
   * This method takes a MethodCallExpr as an instance, and check if the method involved is called
   * by an incomplete synthetic class. It should be noted that an incomplete synthetic class is
   * different from a non-existing synthetic class. In this context, an incomplete synthetic class
   * is a compilable class but missing some methods.
   *
   * @param method a MethodCallExpr instance
   * @return true if the method involved is called by an incomplete synthetic class
   */
  public static boolean calledByAnIncompleteSyntheticClass(MethodCallExpr method) {
    if (calledByAnUnsolvedSymbol(method)) {
      return false;
    }
    if (method.getScope().isEmpty()) {
      return false;
    }
    try {
      method.resolve();
      return false;
    } catch (Exception e) {
      return true;
    }
  }

  /**
   * Given a MethodCallExpr instance, this method will return the synthetic class for the method
   * involved. Thus, make sure that the input method actually belongs to an existing synthetic class
   * before calling this method {@link
   * UnsolvedSymbolVisitor#calledByAnIncompleteSyntheticClass(MethodCallExpr)}}
   *
   * @param method the method call to be analyzed
   * @return the name of the synthetic class of that method
   */
  public static @ClassGetSimpleName String getSyntheticClass(MethodCallExpr method) {
    // if calledByAnIncompleteSyntheticClass returns true for this method call, we know that it has
    // a caller.
    ResolvedType callerExpression = method.getScope().get().calculateResolvedType();
    if (callerExpression instanceof ResolvedReferenceType) {
      ResolvedReferenceType referCaller = (ResolvedReferenceType) callerExpression;
      @FullyQualifiedName String callerName = referCaller.getQualifiedName();
      @ClassGetSimpleName String callerSimple = fullyQualifiedToSimple(callerName);
      return callerSimple;
    } else {
      throw new RuntimeException("Unexpected expression: " + callerExpression);
    }
  }

  /**
   * This method converts a @FullyQualifiedName classname to a @ClassGetSimpleName classname. Note
   * that there is warning suppression here. It is safe to claim that if we split
   * a @FullyQualifiedName name by dot ([.]), then the last part is the @ClassGetSimpleName part.
   *
   * @param fullyQualifiedName a @FullyQualifiedName classname
   * @return the @ClassGetSimpleName version of that class
   */
  public static @ClassGetSimpleName String fullyQualifiedToSimple(
      @FullyQualifiedName String fullyQualifiedName) {
    @SuppressWarnings("signature")
    @ClassGetSimpleName String simpleName = fullyQualifiedName.substring(fullyQualifiedName.lastIndexOf(".") + 1);
    return simpleName;
  }

  /**
   * Given the name of an unsolved method, this method will return the name of the synthetic return
   * type for that method. The name is in @ClassGetSimpleName form
   *
   * @param methodName the name of a method
   * @return that name in @ClassGetSimpleName form
   */
  public static @ClassGetSimpleName String returnNameForMethod(String methodName) {
    String capitalizedMethodName =
        methodName.substring(0, 1).toUpperCase() + methodName.substring(1);
    @SuppressWarnings("signature")
    @ClassGetSimpleName String returnName = capitalizedMethodName + "ReturnType";
    return returnName;
  }

  /**
   * This method is to update the missingClass list. The reason we have this update is to add a
   * method to an existing class.
   *
   * @param missedClass the class to be updated
   */
  public void updateMissingClass(UnsolvedClass missedClass) {
    Iterator<UnsolvedClass> iterator = missingClass.iterator();
    while (iterator.hasNext()) {
      UnsolvedClass e = iterator.next();
      if (e.getClassName().equals(missedClass.getClassName())) {

        // add new methods
        for (UnsolvedMethod method : missedClass.getMethods()) {
          // this boolean checks if the required method is already inside the related synthetic
          // class. In that case, no need to add another one.
          boolean alreadyHad = false;
          for (UnsolvedMethod classMethod : e.getMethods()) {
            if (classMethod.getReturnType().equals(method.getReturnType())) {
              if (classMethod.getName().equals(method.getName())) {
                alreadyHad = true;
                break;
              }
            }
          }
          if (!alreadyHad) {
            e.addMethod(method);
          }
        }

        // add new fields
        for (String variablesDescription : missedClass.getClassFields()) {
          e.addFields(variablesDescription);
        }
        if (missedClass.getNumberOfTypeVariables() > 0) {
          e.setNumberOfTypeVariables(missedClass.getNumberOfTypeVariables());
        }
        return;
      }
    }
    missingClass.add(missedClass);
  }

  /**
   * The method to update synthetic files. After each run, we might have new synthetic files to be
   * created, or new methods to be added to existing synthetic classes. This method will delete all
   * the synthetic files from the previous run and re-create those files with the input from the
   * current run.
   */
  public void updateSyntheticSourceCode() {
    for (UnsolvedClass missedClass : missingClass) {
      this.deleteOldSyntheticClass(missedClass);
      this.createMissingClass(missedClass);
    }
  }

  /**
   * This method is to delete a synthetic class. If that synthetic class is not created yet, the
   * method will do nothing.
   *
   * @param missedClass a synthetic class to be deleted
   */
  public void deleteOldSyntheticClass(UnsolvedClass missedClass) {
    String classPackage = missedClass.getPackageName();
    String classDirectory = classPackage.replace(".", "/");
    String filePathStr =
        this.rootDirectory + classDirectory + "/" + missedClass.getClassName() + ".java";
    Path filePath = Path.of(filePathStr);
    try {
      Files.delete(filePath);
    } catch (IOException e) {
      // It means that the class that has not been created in the previous run of this visitor
    }
  }

  /**
   * This method create a synthetic file for a class that is not in the source codes. The class will
   * be created in the root directory of the input. All these synthetic files will be deleted when
   * Specimin finishes its run.
   *
   * @param missedClass the class to be added
   */
  public void createMissingClass(UnsolvedClass missedClass) {
    StringBuilder fileContent = new StringBuilder();
    fileContent.append(missedClass);
    String classPackage = missedClass.getPackageName();
    String classDirectory = classPackage.replace(".", "/");
    String filePathStr =
        this.rootDirectory + classDirectory + "/" + missedClass.getClassName() + ".java";
    Path filePath = Paths.get(filePathStr);

    createdClass.add(filePath);
    try {
      Path parentPath = filePath.getParent();
      if (parentPath != null && !Files.exists(parentPath)) {
        Files.createDirectories(parentPath);
      }
      try (BufferedWriter writer =
          new BufferedWriter(new FileWriter(filePath.toFile(), StandardCharsets.UTF_8))) {
        writer.write(fileContent.toString());
      } catch (Exception e) {
        throw new Error(e.getMessage());
      }
    } catch (IOException e) {
      System.out.println("Error creating Java file: " + e.getMessage());
    }
  }

  /**
   * This method capitalizes a string. For example, "hello" will become "Hello".
   *
   * @param string the string to be capitalized
   * @return the capitalized version of the string
   */
  public static String toCapital(String string) {
    return string.substring(0, 1).toUpperCase() + string.substring(1);
  }

  /**
   * This method checks if a string is capitalized
   *
   * @param string the string to be checked
   * @return true if the string is capitalized
   */
  public static boolean isCapital(String string) {
    Character first = string.charAt(0);
    return Character.isUpperCase(first);
  }

  /**
   * This method checks if a string has the form of a class path.
   *
   * @param potentialClassPath the string to be checked
   * @return true if the string is a class path
   */
  public static boolean isAClassPath(String potentialClassPath) {
    List<String> elements = Splitter.onPattern("\\.").splitToList(potentialClassPath);
    ;
    int elementsCount = elements.size();
    return elementsCount > 1 && isCapital(elements.get(elementsCount - 1));
  }

  /**
   * Given the name of a class in the @FullyQualifiedName, this method will create a synthetic class
   * for that class
   *
   * @param fullyName the fully-qualified name of the class
   * @return the corresponding instance of UnsolvedClass
   */
  public static UnsolvedClass getSimpleSyntheticClassFromFullyQualifiedName(
      @FullyQualifiedName String fullyName) {
    if (!isAClassPath(fullyName)) {
      throw new RuntimeException(
          "Check with isAClassPath first before using"
              + " getSimpleSyntheticClassFromFullyQualifiedName");
    }
    String className = fullyQualifiedToSimple(fullyName);
    String packageName = fullyName.replace("." + className, "");
    return new UnsolvedClass(className, packageName);
  }

  /**
   * Checks whether a method call, invoked by a simple class name, is unsolved.
   *
   * @param method the method call to be examined
   * @return true if the method is unsolved and called by a simple class name, otherwise false
   */
  public boolean unsolvedAndCalledByASimpleClassName(MethodCallExpr method) {
    try {
      method.resolve();
      return false;
    } catch (Exception e) {
      Optional<Expression> callerExpression = method.getScope();
      if (callerExpression.isEmpty()) {
        return false;
      }
      return classAndPackageMap.containsKey(callerExpression.get().toString());
    }
  }

  /**
   * Returns the fully-qualified class name version of a method call invoked by a simple class name.
   *
   * @param method the method call invoked by a simple class name
   * @return the String representation of the method call with a fully-qualified class name
   */
  public String toFullyQualifiedCall(MethodCallExpr method) {
    if (!unsolvedAndCalledByASimpleClassName(method)) {
      throw new RuntimeException(
          "Before running convertSimpleCallToFullyQualifiedCall, check if the method call is called"
              + " by a simple class name with calledByASimpleClassName");
    }
    String methodCall = method.toString();
    String classCaller = method.getScope().get().toString();
    String packageOfClass = this.classAndPackageMap.get(classCaller);
    return packageOfClass + "." + methodCall;
  }

  /**
   * This method checks if a method call is static method that is called by a qualified class name.
   * For example, for this call org.package.Class.methodFirst().methodSecond(), this method will
   * return true for "org.package.Class.methodFirst()", but not for
   * "org.package.Class.methodFirst().methodSecond()".
   *
   * @param method the method call to be checked
   * @return true if the method call is not simple and unsolved
   */
  public boolean isAnUnsolvedStaticMethodCalledByAQualifiedClassName(MethodCallExpr method) {
    try {
      method.resolve().getReturnType();
      return false;
    } catch (Exception e) {
      Optional<Expression> callerExpression = method.getScope();
      if (callerExpression.isEmpty()) {
        return false;
      }
      String callerToString = callerExpression.get().toString();
      return isAClassPath(callerToString);
    }
  }

  /**
   * Creates a synthetic class corresponding to a static method called by a qualified class name.
   * Ensure to check with {@link #isAnUnsolvedStaticMethodCalledByAQualifiedClassName} before
   * calling this method.
   *
   * @param methodCall the method call to be used as input. This method call must contain one or
   *     more dot separated identifiers, followed by a single pair of parentheses containing
   *     arguments
   * @param methodArguments the list of arguments for this method call
   */
  public void updateClassSetWithQualifiedStaticMethodCall(
      String methodCall, List<String> methodArguments) {
    // As this code involves complex string operations, we'll use a method call as an example,
    // following its progression through the code.
    // Suppose this is our method call: com.example.MyClass.process()
    // At this point, our method call become: com.example.MyClass.process
    String methodCallWithoutParen = methodCall.substring(0, methodCall.indexOf('('));
    List<String> methodParts = Splitter.onPattern("[.]").splitToList(methodCallWithoutParen);
    int lengthMethodParts = methodParts.size();
    if (lengthMethodParts <= 2) {
      throw new RuntimeException(
          "Need to check the method call with unsolvedAndNotSimple before using"
              + " isAnUnsolvedStaticMethodCalledByAQualifiedClassName");
    }
    String returnTypeClassName = toCapital(methodParts.get(0));
    String packageName = methodParts.get(0);
    // According to the above example, methodName will be process
    String methodName = methodParts.get(lengthMethodParts - 1);
    @SuppressWarnings(
        "signature") // this className is from the second-to-last part of a fully-qualified method
    // call, which is the simple name of a class. In this case, it is MyClass.
    @ClassGetSimpleName String className = methodParts.get(lengthMethodParts - 2);
    // After this loop: returnTypeClassName will be ComExample, and packageName will be com.example
    for (int i = 1; i < lengthMethodParts - 2; i++) {
      returnTypeClassName = returnTypeClassName + toCapital(methodParts.get(i));
      packageName = packageName + "." + methodParts.get(i);
    }
    // At this point, returnTypeClassName will be ComExampleMyClassProcessReturnType
    returnTypeClassName =
        returnTypeClassName + toCapital(className) + toCapital(methodName) + "ReturnType";
    // since returnTypeClassName is just a single long string without any dot in the middle, it will
    // be a simple name.
    @SuppressWarnings("signature")
    @ClassGetSimpleName String thisReturnType = returnTypeClassName;
    UnsolvedClass returnClass = new UnsolvedClass(thisReturnType, packageName);
    UnsolvedMethod newMethod = new UnsolvedMethod(methodName, thisReturnType, methodArguments);
    UnsolvedClass classThatContainMethod = new UnsolvedClass(className, packageName);
    newMethod.setStatic();
    classThatContainMethod.addMethod(newMethod);
    syntheticMethodAndClass.put(newMethod.toString(), classThatContainMethod);
    @SuppressWarnings(
        "signature") // thisReturnType is a @ClassGetSimpleName, so combining it with the
    // packageName will give us the @FullyQualifiedName
    @FullyQualifiedName String returnTypeFullName = packageName + "." + thisReturnType;
    syntheticReturnTypes.add(returnTypeFullName);
    this.updateMissingClass(returnClass);
    this.updateMissingClass(classThatContainMethod);
  }

  /**
   * Based on the Map returned by JavaTypeCorrect, this method updates the types of methods in
   * synthetic classes.
   *
   * @param typeToCorrect the Map to be analyzed
   */
  public void updateTypes(Map<String, String> typeToCorrect) {
    for (String incorrectType : typeToCorrect.keySet()) {
      // convert MethodNameReturnType to methodName
      String involvedMethod =
          incorrectType.substring(0, 1).toLowerCase()
              + incorrectType.substring(1).replace("ReturnType", "");
      UnsolvedClass relatedClass = syntheticMethodAndClass.get(involvedMethod);
      if (relatedClass != null) {
        for (UnsolvedClass syntheticClass : missingClass) {
          if (syntheticClass.getClassName().equals(relatedClass.getClassName())
              && syntheticClass.getPackageName().equals(relatedClass.getPackageName())) {
            syntheticClass.updateMethodByReturnType(
                incorrectType, typeToCorrect.get(incorrectType));
            this.deleteOldSyntheticClass(syntheticClass);
            this.createMissingClass(syntheticClass);
          }
        }
        relatedClass.updateMethodByReturnType(incorrectType, typeToCorrect.get(incorrectType));
      }
      // if the above condition is not met, then this incorrectType is a synthetic type for the
      // fields of the parent class rather than the return type of some methods
      else {
        for (UnsolvedClass unsolClass : missingClass) {
          for (String parentClass : classAndItsParent.values()) {
            if (unsolClass.getClassName().equals(parentClass)) {
              unsolClass.updateFieldByType(incorrectType, typeToCorrect.get(incorrectType));
              this.deleteOldSyntheticClass(unsolClass);
              this.createMissingClass(unsolClass);
            }
          }
        }
      }
    }
  }

  /**
   * Given the name of a class, this method will based on the map classAndItsParent to find the name
   * of the super class of the input class
   *
   * @param className the name of the class to be taken as the input
   * @return the name of the super class of the input class
   */
  public @ClassGetSimpleName String getParentClass(String className) {
    if (classAndItsParent.containsKey(className)) {
      return classAndItsParent.get(className);
    } else {
      throw new RuntimeException("Unfound parent for this class: " + className);
    }
  }
}
