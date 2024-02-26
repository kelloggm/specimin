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
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.expr.ThisExpr;
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
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.utils.Pair;
import com.google.common.base.Ascii;
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
   * Flag for whether or not to print debugging output. Should always be false except when you are
   * actively debugging.
   */
  private static final boolean DEBUG = true;

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
  private final ArrayDeque<Set<String>> localVariables = new ArrayDeque<Set<String>>();

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
  private final Set<UnsolvedClassOrInterface> missingClass = new HashSet<>();

  /** The same as the root being used in SpeciminRunner */
  private final String rootDirectory;

  /**
   * This instance maps the name of the return type of a synthetic method with the synthetic class
   * of that method
   */
  private final Map<String, UnsolvedClassOrInterface> syntheticMethodReturnTypeAndClass =
      new HashMap<>();

  /**
   * This instance maps the name of a synthetic type with the class where there is a field declared
   * with that type
   */
  private final Map<String, UnsolvedClassOrInterface> syntheticTypeAndClass = new HashMap<>();

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

  /** The list of existing files in the input codebase. */
  private Set<Path> setOfExistingFiles;

  /**
   * Mapping of statically imported members where keys are the imported members and values are their
   * corresponding classes.
   */
  private final Map<String, @FullyQualifiedName String> staticImportedMembersMap = new HashMap<>();

  /** New files that should be added to the list of target files for the next iteration. */
  private final Set<String> addedTargetFiles = new HashSet<>();

  /** Stores the sets of method declarations in the currently visiting classes. */
  private final ArrayDeque<Set<MethodDeclaration>> declaredMethod = new ArrayDeque<>();

  /** Maps the name of a class to the list of unsolved interface that it implements. */
  private final Map<@ClassGetSimpleName String, List<@ClassGetSimpleName String>>
      classToItsUnsolvedInterface = new HashMap<>();

  /** List of signatures of target methods as specified by users. */
  private final Set<String> targetMethodsSignatures;

  /**
   * Fields and methods that could be called inside the target methods. We call them potential-used
   * because the usage check is simply based on the simple names of those members.
   */
  private final Set<String> potentialUsedMembers = new HashSet<>();

  /**
   * Check whether the visitor is inside the declaration of a target method. Symbols inside the
   * declarations of target methods will be solved if they have one of the following types:
   * ClassOrInterfaceType, Parameters, VariableDeclarator, MethodCallExpr, FieldAccessExpr,
   * ExplicitConstructorInvocationStmt, NameExpr, MethodDeclaration, and ObjectCreationExpr.
   */
  private boolean insideTargetMethod = false;

  /**
   * Check whether the visitor is inside the declaration of a member that could be used by the
   * target methods. Symbols inside the declarations of potentially-used members will be solved if
   * they have one of the following types: ClassOrInterfaceType, Parameters, and VariableDeclarator.
   */
  private boolean insidePotentialUsedMember = false;

  /** The qualified name of the current class. */
  private String currentClassQualifiedName = "";

  /**
   * Create a new UnsolvedSymbolVisitor instance
   *
   * @param rootDirectory the root directory of the input files
   * @param setOfExistingFiles the set of existing files in the input codebase
   * @param targetMethodsSignatures the list of signatures of target methods as specified by the
   *     user.
   */
  public UnsolvedSymbolVisitor(
      String rootDirectory, Set<Path> setOfExistingFiles, List<String> targetMethodsSignatures) {
    this.rootDirectory = rootDirectory;
    this.gotException = true;
    this.setOfExistingFiles = setOfExistingFiles;
    this.targetMethodsSignatures = new HashSet<>();
    this.targetMethodsSignatures.addAll(targetMethodsSignatures);
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

  /**
   * Set gotException to false. This method is to be used at the beginning of each iteration of the
   * visitor.
   */
  public void setExceptionToFalse() {
    gotException = false;
  }

  /**
   * Get the set of target files that should be added for the next iteration.
   *
   * @return the value of addedTargetFiles.
   */
  public Set<String> getAddedTargetFiles() {
    return addedTargetFiles;
  }

  @Override
  public Node visit(ImportDeclaration decl, Void arg) {
    if (decl.isAsterisk()) {
      throw new RuntimeException(
          "A wildcard import statement found. Please use explicit import" + " statements.");
    }
    if (decl.isStatic()) {
      String name = decl.getNameAsString();
      @SuppressWarnings(
          "signature") // since this is from an import statement, this is a fully qualified class
      // name
      @FullyQualifiedName String className = name.substring(0, name.lastIndexOf("."));
      String elementName = name.replace(className + ".", "");
      staticImportedMembersMap.put(elementName, className);
    }
    return super.visit(decl, arg);
  }

  @Override
  public Visitable visit(PackageDeclaration node, Void arg) {
    this.currentPackage = node.getNameAsString();
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration node, Void arg) {
    // This is a special case, since the symbols of a ClassOrInterfaceDeclarations will be solved
    // regardless of being inside target methods or potentially-used members.
    SimpleName nodeName = node.getName();
    className = nodeName.asString();

    if (node.isNestedType()) {
      this.currentClassQualifiedName += "." + node.getName().asString();
    } else {
      this.currentClassQualifiedName = node.getFullyQualifiedName().orElseThrow();
    }
    if (node.getExtendedTypes().isNonEmpty()) {
      // note that since Specimin does not have access to the classpaths of the project, all the
      // unsolved methods related to inheritance will be placed in the parent class, even if there
      // is a grandparent class and so forth.
      SimpleName superClassSimpleName = node.getExtendedTypes().get(0).getName();
      classAndItsParent.put(className, superClassSimpleName.asString());
    }

    NodeList<ClassOrInterfaceType> implementedTypes = node.getImplementedTypes();
    // Not sure why getExtendedTypes return a list, since a class can only extends at most one class
    // in Java.
    NodeList<ClassOrInterfaceType> extendedAndImplementedTypes = node.getExtendedTypes();
    extendedAndImplementedTypes.addAll(implementedTypes);
    for (ClassOrInterfaceType implementedOrExtended : extendedAndImplementedTypes) {
      System.out.println("considering implemented or extended type: " + implementedOrExtended);
      String typeName = implementedOrExtended.getName().asString();
      String packageName = getPackageFromClassName(typeName);
      String qualifiedName = packageName + "." + typeName;
      if (classfileIsInOriginalCodebase(qualifiedName)) {
        // add the source codes of the interface or the super class to the list of target files so
        // that UnsolvedSymbolVisitor can solve symbols for that class if needed.
        String filePath = qualifiedNameToFilePath(qualifiedName);
        if (!addedTargetFiles.contains(filePath)) {
          // strictly speaking, there is no exception here. But we set gotException to true so that
          // UnsolvedSymbolVisitor will run at least one more iteration to visit the newly added
          // file.
          gotException();
        }
        addedTargetFiles.add(filePath);
      } else {
        UnsolvedClassOrInterface unsolvedInterface;
        try {
          implementedOrExtended.resolve();
          continue;
        } catch (UnsolvedSymbolException e) {
          // this extended/implemented type is an interface if it is in the declaration of an
          // interface, or if it is used with the "implements" keyword.
          boolean typeIsAnInterface =
              node.isInterface() || implementedTypes.contains(implementedOrExtended);
          if (typeIsAnInterface) {
            unsolvedInterface = new UnsolvedClassOrInterface(typeName, packageName, false, true);
            @SuppressWarnings(
                "signature") // an empty array list is not a list of @ClassGetSimpleName, but since
            // we will add typeName to that list right after the initialization,
            // this code is correct.
            List<@ClassGetSimpleName String> interfaceName =
                classToItsUnsolvedInterface.computeIfAbsent(className, k -> new ArrayList<>());
            interfaceName.add(typeName);
          } else {
            unsolvedInterface = new UnsolvedClassOrInterface(typeName, packageName);
          }
        }
        updateMissingClass(unsolvedInterface);
      }
    }

    addTypeVariableScope(node.getTypeParameters());
    declaredMethod.addFirst(new HashSet<>(node.getMethods()));
    Visitable result = super.visit(node, arg);
    typeVariables.removeFirst();
    declaredMethod.removeFirst();

    if (node.isNestedType()) {
      this.currentClassQualifiedName =
          this.currentClassQualifiedName.substring(
              0, this.currentClassQualifiedName.lastIndexOf('.'));
    } else {
      this.currentClassQualifiedName = "";
    }
    return result;
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt node, Void arg) {
    if (node.isThis()) {
      return super.visit(node, arg);
    }
    if (!insideTargetMethod) {

      return super.visit(node, arg);
    }
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
      UnsolvedClassOrInterface superClass =
          new UnsolvedClassOrInterface(
              getParentClass(className), getPackageFromClassName(getParentClass(className)));
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
    currentLocalVariables.add(node.getParameter().getNameAsString());
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
      Set<String> currentListOfLocals = localVariables.removeFirst();
      currentListOfLocals.add(decl.getNameAsString());
      localVariables.addFirst(currentListOfLocals);
    }
    if (potentialUsedMembers.contains(decl.getName().asString())) {
      insidePotentialUsedMember = true;
    }
    if (!insideTargetMethod && !insidePotentialUsedMember) {
      return super.visit(decl, p);
    }

    // This part is to create synthetic class for the type of decl if needed.
    Type declType = decl.getType();
    if (declType.isVarType()) {
      // nothing to do here. A var type could never be solved.
      Visitable result = super.visit(decl, p);
      insidePotentialUsedMember = false;
      return result;
    }
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
      // Handles the case where the type is a simple class name. Two sub-cases are considered: 1.
      // The class is included among the import statements. 2. The class is not included in the
      // import statements but is in the same directory as the input class. The first sub-case is
      // addressed by the visit method for ImportDeclaration.
      else if (!classAndPackageMap.containsKey(typeAsString)) {
        @SuppressWarnings("signature") // since this is the simple name case
        @ClassGetSimpleName String className = typeAsString;
        String packageName = this.currentPackage;
        UnsolvedClassOrInterface newClass = new UnsolvedClassOrInterface(className, packageName);
        updateMissingClass(newClass);
      }
    }
    Visitable result = super.visit(decl, p);
    insidePotentialUsedMember = false;
    return result;
  }

  @Override
  public Visitable visit(NameExpr node, Void arg) {
    if (!insideTargetMethod) {
      return super.visit(node, arg);
    }
    String name = node.getNameAsString();
    if (fieldNameToClassNameMap.containsKey(name)) {
      potentialUsedMembers.add(name);
      try {
        // check if the type is resolved and does not extend any unresolved type.
        ResolvedType nameExprType = node.resolve().getType();
        if (nameExprType.isReferenceType()) {
          ResolvedReferenceType nameExprReferenceType = nameExprType.asReferenceType();
          nameExprReferenceType.getAllAncestors();
          // check if all the type parameters are resolved.
          if (!hasResolvedTypeParameters(nameExprReferenceType)) {
            gotException();
          }
        }
      } catch (UnsolvedSymbolException e) {
        gotException();
      }
      return super.visit(node, arg);
    }
    // this condition checks if this NameExpr is a statically imported field
    else if (staticImportedMembersMap.containsKey(name)) {
      try {
        node.resolve();
      } catch (UnsolvedSymbolException e) {
        @FullyQualifiedName String className = staticImportedMembersMap.get(name);
        String fullyQualifiedFieldSignature = className + "." + name;
        updateClassSetWithQualifiedFieldSignature(fullyQualifiedFieldSignature, true, true);
        return super.visit(node, arg);
      }
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
    String methodQualifiedSignature =
        this.currentClassQualifiedName
            + "#"
            + TargetMethodFinderVisitor.removeMethodReturnType(
                node.getDeclarationAsString(false, false, false));
    if (targetMethodsSignatures.contains(methodQualifiedSignature)) {
      insideTargetMethod = true;
    }
    addTypeVariableScope(node.getTypeParameters());
    Visitable result = super.visit(node, arg);
    typeVariables.removeFirst();
    if (targetMethodsSignatures.contains(methodQualifiedSignature)) {
      insideTargetMethod = false;
    }
    return result;
  }

  @Override
  public Visitable visit(MethodDeclaration node, Void arg) {
    String methodQualifiedSignature =
        this.currentClassQualifiedName
            + "#"
            + TargetMethodFinderVisitor.removeMethodReturnType(
                node.getDeclarationAsString(false, false, false));
    String methodSimpleName = node.getName().asString();
    if (targetMethodsSignatures.contains(methodQualifiedSignature)) {
      insideTargetMethod = true;
      Visitable result = processMethodDeclaration(node);
      insideTargetMethod = false;
      return result;
    } else if (potentialUsedMembers.contains(methodSimpleName)) {
      insidePotentialUsedMember = true;
      Visitable result = processMethodDeclaration(node);
      insidePotentialUsedMember = false;
      return result;
    } else if (insideTargetMethod) {
      return processMethodDeclaration(node);
    } else {
      return super.visit(node, arg);
    }
  }

  @Override
  public Visitable visit(FieldAccessExpr node, Void p) {
    if (!insideTargetMethod) {
      return super.visit(node, p);
    }
    potentialUsedMembers.add(node.getNameAsString());
    boolean canBeSolved = canBeSolved(node);
    if (isASuperCall(node) && !canBeSolved) {
      updateSyntheticClassForSuperCall(node);
    } else if (canBeSolved) {
      return super.visit(node, p);
    } else if (isAQualifiedFieldSignature(node.toString())) {
      updateClassSetWithQualifiedFieldSignature(node.toString(), true, false);
    } else if (unsolvedFieldCalledByASimpleClassName(node)) {
      String simpleClassName = node.getScope().toString();
      String fullyQualifiedCall = getPackageFromClassName(simpleClassName) + "." + node;
      updateClassSetWithQualifiedFieldSignature(fullyQualifiedCall, true, false);
    } else if (canBeSolved(node.getScope())) {
      // check if this unsolved field belongs to a synthetic class.
      if (!belongsToARealClassFile(node)) {
        updateSyntheticClassWithNonStaticFields(node);
      } else {
        // since we have checked whether node.getScope() can be solved, this call is safe.
        addedTargetFiles.add(
            qualifiedNameToFilePath(
                node.getScope().calculateResolvedType().asReferenceType().getQualifiedName()));
      }
    }

    try {
      node.resolve();
    } catch (UnsolvedSymbolException e) {
      // for a qualified name field access such as org.sample.MyClass.field, org.sample will also be
      // considered FieldAccessExpr.
      if (isAClassPath(node.getScope().toString())) {
        gotException();
      }
    }
    return super.visit(node, p);
  }

  @Override
  public Visitable visit(MethodCallExpr method, Void p) {
    if (!insideTargetMethod) {
      return super.visit(method, p);
    }
    potentialUsedMembers.add(method.getName().asString());
    boolean canBeSolved = canBeSolved(method);
    if (canBeSolved && isFromAJarFile(method)) {
      updateClassesFromJarSourcesForMethodCall(method);
      return super.visit(method, p);
    }
    // we will wait for the next run to solve this method call
    if (!canSolveParameters(method)) {
      return super.visit(method, p);
    }
    if (isASuperCall(method) && !canBeSolved) {
      updateSyntheticClassForSuperCall(method);
      return super.visit(method, p);
    }
    if (isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method)) {
      updateClassSetWithQualifiedStaticMethodCall(
          method.toString(), getArgumentsFromMethodCall(method));
    } else if (calledByAnIncompleteClass(method)) {
      String qualifiedNameOfIncompleteClass = getIncompleteClass(method);
      if (classfileIsInOriginalCodebase(qualifiedNameOfIncompleteClass)) {
        addedTargetFiles.add(qualifiedNameToFilePath(qualifiedNameOfIncompleteClass));
      } else {
        @ClassGetSimpleName String incompleteClassName = fullyQualifiedToSimple(qualifiedNameOfIncompleteClass);
        updateUnsolvedClassOrInterfaceWithMethod(method, incompleteClassName, "", false);
      }
    } else if (unsolvedAndCalledByASimpleClassName(method)) {
      String methodFullyQualifiedCall = toFullyQualifiedCall(method);
      updateClassSetWithQualifiedStaticMethodCall(
          methodFullyQualifiedCall, getArgumentsFromMethodCall(method));
    } else if (staticImportedMembersMap.containsKey(method.getNameAsString())) {
      String methodName = method.getNameAsString();
      @FullyQualifiedName String className = staticImportedMembersMap.get(methodName);
      String methodFullyQualifiedCall = className + "." + methodName;
      // everything inside the (...) will be trimmed
      updateClassSetWithQualifiedStaticMethodCall(
          methodFullyQualifiedCall + "()", getArgumentsFromMethodCall(method));
    } else if (haveNoScopeOrCallByThisKeyword(method)) {
      // in this case, the method must be declared inside the interface or the superclass that the
      // current class extends/implements.
      if (!declaredInCurrentClass(method)) {
        if (classToItsUnsolvedInterface.containsKey(className)) {
          List<@ClassGetSimpleName String> relevantInterfaces =
              classToItsUnsolvedInterface.get(className);
          // Since these are unsolved interfaces, we have no ideas which one of them contains the
          // signature for the current method, thus we will put the signature in the last interface.
          String unsolvedInterface = relevantInterfaces.get(relevantInterfaces.size() - 1);
          updateUnsolvedClassOrInterfaceWithMethod(method, unsolvedInterface, "", true);
        } else if (classAndItsParent.containsKey(className)) {
          String parentName = classAndItsParent.get(className);
          updateUnsolvedClassOrInterfaceWithMethod(method, parentName, "", false);
        }
      }
    }

    // Though this structure looks a bit silly, it is intentional
    // that these 4 calls to getException() produce different stacktraces,
    // which is very helpful for debugging infinite loops.
    if (!canBeSolved) {
      gotException();
    } else if (calledByAnUnsolvedSymbol(method)) {
      gotException();
    } else if (calledByAnIncompleteClass(method)) {
      gotException();
    } else if (isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method)) {
      gotException();
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
    if (isTypeVar(typeExpr.getName().asString())) {
      return super.visit(typeExpr, p);
    }
    // type belonging to a class declaration will be handled by the visit method for
    // ClassOrInterfaceDeclaration
    if (typeExpr.getParentNode().get() instanceof ClassOrInterfaceDeclaration) {
      return super.visit(typeExpr, p);
    }
    if (!insideTargetMethod && !insidePotentialUsedMember) {
      return super.visit(typeExpr, p);
    }
    try {
      // resolve() checks whether this type is resolved. getAllAncestor() checks whether this type
      // extends or implements a resolved class/interface.
      typeExpr.resolve().getAllAncestors();
      return super.visit(typeExpr, p);
    }
    /*
     * 1. If the class file is in the codebase but extends/implements a class/interface not in the codebase, we got UnsolvedSymbolException.
     * 2. If the class file is not in the codebase yet, we also got UnsolvedSymbolException.
     * 3. If the class file is not in the codebase and used by an anonymous class, we got UnsupportedOperationException.
     * 4. If the class file is in the codebase but the type variables are missing, we got IllegalArgumentException.
     */
    catch (UnsolvedSymbolException | UnsupportedOperationException | IllegalArgumentException e) {
      // this is for case 1. By adding the class file to the list of target files,
      // UnsolvedSymbolVisitor will take care of the unsolved extension in its next iteration.
      String qualifiedName =
          getPackageFromClassName(typeExpr.getNameAsString()) + "." + typeExpr.getNameAsString();
      if (classfileIsInOriginalCodebase(qualifiedName)) {
        addedTargetFiles.add(qualifiedNameToFilePath(qualifiedName));
        gotException();
        return super.visit(typeExpr, p);
      }

      // below is for other three cases.

      // This method only updates type variables for unsolved classes. Other problems causing a
      // class to be unsolved will be fixed by other methods.
      Optional<NodeList<Type>> typeArguments = typeExpr.getTypeArguments();
      UnsolvedClassOrInterface classToUpdate;
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
        String className = typeRawName.substring(typeRawName.lastIndexOf(".") + 1);
        classToUpdate = new UnsolvedClassOrInterface(className, packageName);
      } else {
        String packageName = getPackageFromClassName(typeRawName);
        classToUpdate = new UnsolvedClassOrInterface(typeRawName, packageName);
      }
      classToUpdate.setNumberOfTypeVariables(numberOfArguments);
      updateMissingClass(classToUpdate);
      gotException();
    }
    return super.visit(typeExpr, p);
  }

  @Override
  public Visitable visit(Parameter parameter, Void p) {
    if (!insidePotentialUsedMember && !insideTargetMethod) {
      return super.visit(parameter, p);
    }
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
      if (!parameter.getType().isUnknownType()) {
        handleParameterResolveFailure(parameter);
        gotException();
      }
    }
    return super.visit(parameter, p);
  }

  @Override
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    if (!insideTargetMethod) {
      return super.visit(newExpr, p);
    }
    SimpleName typeName = newExpr.getType().getName();
    String type = typeName.asString();
    if (canBeSolved(newExpr)) {
      if (isFromAJarFile(newExpr)) {
        updateClassesFromJarSourcesForObjectCreation(newExpr);
      }
      return super.visit(newExpr, p);
    }
    gotException();
    try {
      List<String> argumentsCreation = getArgumentsFromObjectCreation(newExpr);
      UnsolvedMethod creationMethod = new UnsolvedMethod("", type, argumentsCreation);
      updateUnsolvedClassWithClassName(type, false, false, creationMethod);
    } catch (Exception q) {
      // can not solve the parameters for this object creation in this current run
    }
    return super.visit(newExpr, p);
  }

  /**
   * Converts a qualified class name into a relative file path. Angle brackets for type variables
   * are permitted in the input.
   *
   * @param qualifiedName The qualified name of the class.
   * @return The relative file path corresponding to the qualified name.
   */
  public String qualifiedNameToFilePath(String qualifiedName) {
    String filePath = qualifiedName.replace(".", "/");
    if (filePath.contains("<")) {
      filePath = filePath.substring(filePath.indexOf("<"));
    }
    filePath = filePath + ".java";
    return filePath;
  }

  /**
   * Given a ResolvedReferenceType, this method checks if all of the type parameters of that type
   * are resolved.
   *
   * @param resolvedReferenceType a resolved reference type
   * @return true if resolvedReferenceType has no unresolved type parameters.
   */
  public boolean hasResolvedTypeParameters(ResolvedReferenceType resolvedReferenceType) {
    for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> typeParameter :
        resolvedReferenceType.getTypeParametersMap()) {
      ResolvedType parameterType = typeParameter.b;
      if (parameterType.isReferenceType()) {
        try {
          // check if parameterType extends any unresolved type.
          parameterType.asReferenceType().getAllAncestors();
        } catch (UnsolvedSymbolException e) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Given a method call, this method checks if that method call is declared in the currently
   * visiting class.
   *
   * @param method the method call to be checked
   * @return true if method is declared in the current clases
   */
  public boolean declaredInCurrentClass(MethodCallExpr method) {
    for (Set<MethodDeclaration> methodDeclarationSet : declaredMethod) {
      for (MethodDeclaration methodDeclared : methodDeclarationSet) {
        if (!methodDeclared.getName().asString().equals(method.getName().asString())) {
          continue;
        }
        List<String> methodTypesOfParameters = getArgumentsFromMethodCall(method);
        NodeList<Parameter> methodDeclaredParameters = methodDeclared.getParameters();
        List<String> methodDeclaredTypesOfParameters = new ArrayList<>();
        for (Parameter parameter : methodDeclaredParameters) {
          try {
            ResolvedType parameterTypeResolved = parameter.getType().resolve();
            if (parameterTypeResolved.isPrimitive()) {
              methodDeclaredTypesOfParameters.add(parameterTypeResolved.asPrimitive().name());
            } else if (parameterTypeResolved.isReferenceType()) {
              methodDeclaredTypesOfParameters.add(
                  parameterTypeResolved.asReferenceType().getQualifiedName());
            }
          } catch (UnsolvedSymbolException e) {
            // UnsolvedSymbolVisitor will not create any synthetic class at this iteration.
            return false;
          }
        }
        if (methodDeclaredTypesOfParameters.equals(methodTypesOfParameters)) {
          // TODO: this test is too strict, because it does not consider subtyping.
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Given a field access expression, this method determines whether the field is declared in one of
   * the original class file in the codebase (instead of a synthetic class).
   *
   * @param node a FieldAccessExpr instance
   * @return true if the field is inside an original class file
   */
  public boolean belongsToARealClassFile(FieldAccessExpr node) {
    Expression nodeScope = node.getScope();
    String filePath =
        rootDirectory + nodeScope.calculateResolvedType().describe().replace(".", "/");
    if (filePath.contains("<")) {
      filePath = filePath.substring(0, filePath.indexOf("<"));
    }
    filePath = filePath + ".java";
    return setOfExistingFiles.contains(Path.of(filePath).toAbsolutePath().normalize());
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
      UnsolvedClassOrInterface newClass =
          getSimpleSyntheticClassFromFullyQualifiedName(parameterInString);
      updateMissingClass(newClass);

    } else {
      // since it is unsolved, it could not be a primitive type
      @ClassGetSimpleName String className = parameter.getType().asClassOrInterfaceType().getName().asString();
      if (parameter.getParentNode().isPresent()
          && parameter.getParentNode().get() instanceof CatchClause) {
        updateUnsolvedClassWithClassName(className, true, false);
      } else {
        updateUnsolvedClassWithClassName(className, false, false);
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
    for (ReferenceType param : parameter.getType().asUnionType().getElements()) {
      try {
        param.resolve();
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        // since this type is unsolved, it could not be a primitive type
        @ClassGetSimpleName String typeName = param.getElementType().asClassOrInterfaceType().getName().asString();
        UnsolvedClassOrInterface newClass = updateUnsolvedClassWithClassName(typeName, true, false);
        updateMissingClass(newClass);
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
   * Given an instance of MethodCallExpr, this method checks if that method has no scope or called
   * by the "this" keyword.
   *
   * @param methodCall the method call to be checked.
   * @return true if methodCall has no scope or called by a "this" keyword.
   */
  private boolean haveNoScopeOrCallByThisKeyword(MethodCallExpr methodCall) {
    Optional<Expression> scope = methodCall.getScope();
    if (scope.isEmpty()) {
      return true;
    }
    return (scope.get() instanceof ThisExpr);
  }

  /**
   * Given a MethodDeclaration instance, this method checks if that MethodDeclaration is inside an
   * object creation expression.
   *
   * @param decl a MethodDeclaration instance
   * @return true if decl is inside an object creation expression
   */
  private boolean insideAnObjectCreation(MethodDeclaration decl) {
    while (decl.getParentNode().isPresent()) {
      Node parent = decl.getParentNode().get();
      if (parent instanceof ObjectCreationExpr) {
        return true;
      }
      if (parent instanceof ClassOrInterfaceDeclaration) {
        return false;
      }
      if (parent instanceof EnumConstantDeclaration) {
        return false;
      }
      if (parent instanceof EnumDeclaration) {
        return false;
      }
    }
    throw new RuntimeException("Got a method declaration with no class!");
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
   * @param updatingInterface true if this method is being used to update an interface, false for
   *     updating classes
   */
  public void updateUnsolvedClassOrInterfaceWithMethod(
      Node method,
      @ClassGetSimpleName String className,
      @ClassGetSimpleName String desiredReturnType,
      boolean updatingInterface) {
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
    UnsolvedMethod thisMethod;
    if (updatingInterface) {
      thisMethod = new UnsolvedMethod(methodName, returnType, listOfParameters, true);
    } else {
      thisMethod = new UnsolvedMethod(methodName, returnType, listOfParameters);
    }

    UnsolvedClassOrInterface missingClass =
        updateUnsolvedClassWithClassName(className, false, false, thisMethod);
    syntheticMethodReturnTypeAndClass.put(returnType, missingClass);

    // if the return type is not specified, a synthetic return type will be created. This part of
    // codes creates the corresponding class for that synthetic return type
    if (desiredReturnType.equals("")) {
      @SuppressWarnings(
          "signature") // returnType is a @ClassGetSimpleName, so combining it with the package will
      // give us the fully-qualified name
      @FullyQualifiedName String packageName = missingClass.getPackageName() + "." + returnType;
      syntheticReturnTypes.add(packageName);
      UnsolvedClassOrInterface returnTypeForThisMethod =
          new UnsolvedClassOrInterface(returnType, missingClass.getPackageName());
      this.updateMissingClass(returnTypeForThisMethod);
      classAndPackageMap.put(
          returnTypeForThisMethod.getClassName(), returnTypeForThisMethod.getPackageName());
    }
  }

  /**
   * Processes a MethodDeclaration by creating necessary synthetic classes for the declaration to be
   * resolved and updating the records of local variables and type variables accordingly. This
   * method also visits that MethodDeclaration input.
   *
   * @param node The MethodDeclaration to be used as input.
   * @return A Visitable object representing the MethodDeclaration.
   */
  public Visitable processMethodDeclaration(MethodDeclaration node) {
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
        updateUnsolvedClassWithClassName(nodeTypeSimpleForm, false, false);
      }
    }

    if (!insideAnObjectCreation(node)) {
      SimpleName classNodeSimpleName = getSimpleNameOfClass(node);
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
        updateUnsolvedClassOrInterfaceWithMethod(
            node, nameOfClass, toSimpleName(nodeTypeAsString), false);
      }
    }
    Set<String> currentLocalVariables = getParameterFromAMethodDeclaration(node);
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, null);
    localVariables.removeFirst();
    typeVariables.removeFirst();
    return result;
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
    UnsolvedClassOrInterface missingClass = new UnsolvedClassOrInterface(className, packageName);
    UnsolvedMethod thisMethod = new UnsolvedMethod(methodName, returnType, argumentsList);
    missingClass.addMethod(thisMethod);
    syntheticMethodReturnTypeAndClass.put(returnType, missingClass);
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
   * @param isUpdatingInterface indicates whether this method is being used to update an interface
   * @return the newly-created UnsolvedClass method, for further processing. This output may be
   *     ignored.
   */
  public UnsolvedClassOrInterface updateUnsolvedClassWithClassName(
      @ClassGetSimpleName String nameOfClass,
      boolean isExceptionType,
      boolean isUpdatingInterface,
      UnsolvedMethod... unsolvedMethods) {
    // if the name of the class is not present among import statements, we assume that this unsolved
    // class is in the same directory as the current class
    String packageName = getPackageFromClassName(nameOfClass);
    UnsolvedClassOrInterface result;
    if (isUpdatingInterface) {
      result = new UnsolvedClassOrInterface(nameOfClass, packageName, isExceptionType, true);
    } else {
      result = new UnsolvedClassOrInterface(nameOfClass, packageName, isExceptionType);
    }
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
    UnsolvedClassOrInterface missingClass = new UnsolvedClassOrInterface(className, packageName);
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
  public Set<String> getParameterFromAMethodDeclaration(MethodDeclaration decl) {
    Set<String> setOfParameters = new HashSet<>();
    for (Parameter parameter : decl.getParameters()) {
      setOfParameters.add(parameter.getName().asString());
    }
    return setOfParameters;
  }

  /**
   * Given a non-static and unsolved field access expression, this method will update the
   * corresponding synthetic class.
   *
   * @param field a non-static field access expression
   */
  public void updateSyntheticClassWithNonStaticFields(FieldAccessExpr field) {
    Expression caller = field.getScope();
    String fullyQualifiedClassName = caller.calculateResolvedType().describe();
    int indexOfAngleBracket = fullyQualifiedClassName.indexOf('<');
    if (indexOfAngleBracket != -1) {
      fullyQualifiedClassName = fullyQualifiedClassName.substring(0, indexOfAngleBracket);
    }
    String fieldQualifedSignature = fullyQualifiedClassName + "." + field.getNameAsString();
    updateClassSetWithQualifiedFieldSignature(fieldQualifedSignature, false, false);
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
      updateUnsolvedClassOrInterfaceWithMethod(
          expr.asMethodCallExpr(),
          getParentClass(className),
          methodAndReturnType.getOrDefault(expr.asMethodCallExpr().getNameAsString(), ""),
          false);
    } else if (expr instanceof FieldAccessExpr) {
      String nameAsString = expr.asFieldAccessExpr().getNameAsString();
      updateUnsolvedSuperClassWithFields(
          nameAsString,
          getParentClass(className),
          getPackageFromClassName(getParentClass(className)));
    } else if (expr instanceof NameExpr) {
      String nameAsString = expr.asNameExpr().getNameAsString();
      updateUnsolvedSuperClassWithFields(
          nameAsString,
          getParentClass(className),
          getPackageFromClassName(getParentClass(className)));
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
  public void updateUnsolvedSuperClassWithFields(
      String var, @ClassGetSimpleName String className, String packageName) {
    UnsolvedClassOrInterface relatedClass = new UnsolvedClassOrInterface(className, packageName);
    if (variablesAndDeclaration.containsKey(var)) {
      String variableExpression = variablesAndDeclaration.get(var);
      relatedClass.addFields(variableExpression);
      updateMissingClass(relatedClass);
    } else {
      // since it is just simple string combination, it is a simple name
      @SuppressWarnings("signature")
      @ClassGetSimpleName String variableType = "SyntheticTypeFor" + toCapital(var);
      UnsolvedClassOrInterface varType = new UnsolvedClassOrInterface(variableType, packageName);
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
    for (Set<String> varSet : localVariables) {
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
   * Given a method declaration, this method will get the name of the class in which the method was
   * declared.
   *
   * @param node the method declaration for input.
   * @return the name of the class to which that declaration belongs.
   */
  private SimpleName getSimpleNameOfClass(MethodDeclaration node) {
    SimpleName classNodeSimpleName;
    Node parentNode = node.getParentNode().get();
    if (parentNode instanceof EnumConstantDeclaration) {
      classNodeSimpleName = ((EnumDeclaration) parentNode.getParentNode().get()).getName();
    } else if (parentNode instanceof EnumDeclaration) {
      classNodeSimpleName = ((EnumDeclaration) parentNode).getName();
    } else if (parentNode instanceof ClassOrInterfaceDeclaration) {
      classNodeSimpleName = ((ClassOrInterfaceDeclaration) parentNode).getName();
    } else {
      throw new RuntimeException("Unexpected parent node: " + parentNode);
    }
    return classNodeSimpleName;
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
   * Given a class name, this method returns the corresponding package name.
   *
   * @param className the name of a class.
   * @return the package of that class.
   */
  public String getPackageFromClassName(String className) {
    if (className.contains("<")) {
      className = className.substring(0, className.indexOf("<"));
    }
    return classAndPackageMap.getOrDefault(className, currentPackage);
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
      System.out.println(e);
      return false;
    }
  }

  /**
   * This method takes a MethodCallExpr as an instance, and check if the method involved is called
   * by an incomplete class. An incomplete class could either be an original class with unsolved
   * symbols or a synthetic class that need to be updated.
   *
   * @param method a MethodCallExpr instance
   * @return true if the method involved is called by an incomplete class
   */
  public static boolean calledByAnIncompleteClass(MethodCallExpr method) {
    if (calledByAnUnsolvedSymbol(method)) {
      return false;
    }
    if (method.getScope().isEmpty()) {
      return false;
    }
    try {
      // use an additional getReturnType() will check the solvability of the method more
      // comprehensively. We need to do this because if the return type isn't explicitly shown
      // when the method is called, the method might be mistakenly perceived as solved even if the
      // return type remains unsolved.
      method.resolve().getReturnType();
      return false;
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      if (e instanceof UnsolvedSymbolException) {
        return true;
      }
      // UnsupportedOperationException is for when the types could not be solved at all, such as
      // var or wildcard types.
      return false;
    }
  }

  /**
   * Given a MethodCallExpr instance, this method will return the incomplete class for the method
   * involved. Thus, make sure that the input method actually belongs to an incomplete class before
   * calling this method {@link UnsolvedSymbolVisitor#calledByAnIncompleteClass(MethodCallExpr)}
   * (MethodCallExpr)}}. An incomplete class is either an original class with unsolved symbols or a
   * synthetic class that needs to be updated.
   *
   * @param method the method call to be analyzed
   * @return the name of the synthetic class of that method
   */
  public static @FullyQualifiedName String getIncompleteClass(MethodCallExpr method) {
    // if calledByAnIncompleteClass returns true for this method call, we know that it has
    // a caller.
    ResolvedType callerExpression = method.getScope().get().calculateResolvedType();
    if (callerExpression instanceof ResolvedReferenceType) {
      ResolvedReferenceType referCaller = (ResolvedReferenceType) callerExpression;
      @FullyQualifiedName String callerName = referCaller.getQualifiedName();
      return callerName;
    } else if (callerExpression instanceof ResolvedLambdaConstraintType) {
      // an example of ConstraintType is the type of "e" in this expression: myMap.map(e ->
      // e.toString())
      @FullyQualifiedName String boundedQualifiedType =
          callerExpression.asConstraintType().getBound().asReferenceType().getQualifiedName();
      return boundedQualifiedType;
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
    String capitalizedMethodName = toCapital(methodName);
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
  public void updateMissingClass(UnsolvedClassOrInterface missedClass) {
    String qualifiedName = missedClass.getQualifiedClassName();
    // If an original class from the input codebase is used with unsolved type parameters, it may be
    // misunderstood as an unresolved class.
    if (classfileIsInOriginalCodebase(qualifiedName)) {
      return;
    }
    Iterator<UnsolvedClassOrInterface> iterator = missingClass.iterator();
    while (iterator.hasNext()) {
      UnsolvedClassOrInterface e = iterator.next();
      if (e.equals(missedClass)) {
        // add new methods
        for (UnsolvedMethod method : missedClass.getMethods()) {
          // No need to check for containment, since the methods are stored
          // as a set (which does not permit duplicates).
          e.addMethod(method);
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
   * Given the qualified name of a class, this method determines if the corresponding class file
   * exists in the original input codebase.
   *
   * @param qualifiedName the qualified name of a class.
   * @return true if the corresponding class file is originally in the input codebase.
   */
  public boolean classfileIsInOriginalCodebase(String qualifiedName) {
    String relativeClassPath = qualifiedName.replace(".", "/");
    int indexOfTypeVariables = relativeClassPath.indexOf("<");
    if (indexOfTypeVariables != -1) {
      relativeClassPath = relativeClassPath.substring(0, indexOfTypeVariables);
    }
    relativeClassPath = relativeClassPath + ".java";
    return this.setOfExistingFiles.contains(
        Paths.get(this.rootDirectory + "/" + relativeClassPath).toAbsolutePath());
  }

  /**
   * The method to update synthetic files. After each run, we might have new synthetic files to be
   * created, or new methods to be added to existing synthetic classes. This method will delete all
   * the synthetic files from the previous run and re-create those files with the input from the
   * current run.
   */
  public void updateSyntheticSourceCode() {
    for (UnsolvedClassOrInterface missedClass : missingClass) {
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
  public void deleteOldSyntheticClass(UnsolvedClassOrInterface missedClass) {
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
  public void createMissingClass(UnsolvedClassOrInterface missedClass) {
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
    return Ascii.toUpperCase(string.substring(0, 1)) + string.substring(1);
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
    int elementsCount = elements.size();
    return elementsCount > 1
        && isCapital(elements.get(elementsCount - 1))
        // Classpaths cannot contain spaces!
        && elements.stream().noneMatch(s -> s.contains(" "));
  }

  /**
   * Given the name of a class in the @FullyQualifiedName, this method will create a synthetic class
   * for that class
   *
   * @param fullyName the fully-qualified name of the class
   * @return the corresponding instance of UnsolvedClass
   */
  public static UnsolvedClassOrInterface getSimpleSyntheticClassFromFullyQualifiedName(
      @FullyQualifiedName String fullyName) {
    if (!isAClassPath(fullyName)) {
      throw new RuntimeException(
          "Check with isAClassPath first before using"
              + " getSimpleSyntheticClassFromFullyQualifiedName");
    }
    String className = fullyQualifiedToSimple(fullyName);
    String packageName = fullyName.replace("." + className, "");
    return new UnsolvedClassOrInterface(className, packageName);
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
   * Check whether a field, invoked by a simple class name, is unsolved
   *
   * @param field the field to be checked
   * @return true if the field is unsolved and invoked by a simple class name
   */
  public boolean unsolvedFieldCalledByASimpleClassName(FieldAccessExpr field) {
    try {
      field.resolve();
      return false;
    } catch (UnsolvedSymbolException e) {
      // this check is not very comprehensive, since a class can be in lowercase, and a method or
      // field can be in uppercase. But since this is without the jar paths, this is the best we can
      // do.
      return Character.isUpperCase(field.getScope().toString().charAt(0));
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
   * This method checks if a field access expression is a qualified field signature. For example,
   * for this field access expression: org.package.Class.firstField.secondField, this method will
   * return true for "org.package.Class.firstField", but not for
   * "org.package.Class.firstField.secondField".
   *
   * @param field the field access expression to be checked
   * @return true if field is a qualified field signature
   */
  public boolean isAQualifiedFieldSignature(String field) {
    String caller = field.substring(0, field.lastIndexOf("."));
    return isAClassPath(caller);
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
    UnsolvedClassOrInterface returnClass =
        new UnsolvedClassOrInterface(thisReturnType, packageName);
    UnsolvedMethod newMethod = new UnsolvedMethod(methodName, thisReturnType, methodArguments);
    UnsolvedClassOrInterface classThatContainMethod =
        new UnsolvedClassOrInterface(className, packageName);
    newMethod.setStatic();
    classThatContainMethod.addMethod(newMethod);
    syntheticMethodReturnTypeAndClass.put(thisReturnType, classThatContainMethod);
    @SuppressWarnings(
        "signature") // thisReturnType is a @ClassGetSimpleName, so combining it with the
    // packageName will give us the @FullyQualifiedName
    @FullyQualifiedName String returnTypeFullName = packageName + "." + thisReturnType;
    syntheticReturnTypes.add(returnTypeFullName);
    this.updateMissingClass(returnClass);
    this.updateMissingClass(classThatContainMethod);
  }

  /**
   * Creates a synthetic class corresponding to a static field called by a qualified class name.
   * Ensure to check with {@link #isAQualifiedFieldSignature(String)} before calling this method.
   *
   * @param fieldExpr the field access expression to be used as input. This field access expression
   *     must be in the form of a qualified class name
   * @param isStatic check whether the field is static
   * @param isFinal check whether the field is final
   */
  public void updateClassSetWithQualifiedFieldSignature(
      String fieldExpr, boolean isStatic, boolean isFinal) {
    // As this code involves complex string operations, we'll use a field access expression as an
    // example,
    // following its progression through the code.
    // Suppose this is our field access expression: com.example.MyClass.myField
    List<String> fieldParts = Splitter.onPattern("[.]").splitToList(fieldExpr);
    int numOfFieldParts = fieldParts.size();
    if (numOfFieldParts <= 2) {
      throw new RuntimeException(
          "Need to check this field access expression with"
              + " isAnUnsolvedStaticFieldCalledByAQualifiedClassName before using this method");
    }
    // this is the synthetic type of the field
    String fieldTypeClassName = toCapital(fieldParts.get(0));
    String packageName = fieldParts.get(0);
    // According to the above example, fieldName will be myField
    String fieldName = fieldParts.get(numOfFieldParts - 1);
    @SuppressWarnings(
        "signature") // this className is from the second-to-last part of a fully-qualified field
    // signature, which is the simple name of a class. In this case, it is MyClass.
    @ClassGetSimpleName String className = fieldParts.get(numOfFieldParts - 2);
    // After this loop: fieldTypeClassName will be ComExample, and packageName will be com.example
    for (int i = 1; i < numOfFieldParts - 2; i++) {
      fieldTypeClassName = fieldTypeClassName + toCapital(fieldParts.get(i));
      packageName = packageName + "." + fieldParts.get(i);
    }
    // At this point, fieldTypeClassName will be ComExampleMyClassMyFieldType
    fieldTypeClassName = fieldTypeClassName + toCapital(className) + toCapital(fieldName) + "Type";
    // since fieldTypeClassName is just a single long string without any dot in the middle, it will
    // be a simple name.
    @SuppressWarnings("signature")
    @ClassGetSimpleName String thisFieldType = fieldTypeClassName;
    UnsolvedClassOrInterface typeClass = new UnsolvedClassOrInterface(thisFieldType, packageName);
    UnsolvedClassOrInterface classThatContainField =
        new UnsolvedClassOrInterface(className, packageName);
    // at this point, fieldDeclaration will become "ComExampleMyClassMyFieldType myField"
    String fieldDeclaration = fieldTypeClassName + " " + fieldName;
    if (isFinal) {
      fieldDeclaration = "final " + fieldDeclaration;
    }
    if (isStatic) {
      // fieldDeclaration will become "static ComExampleMyClassMyFieldType myField = null;"
      fieldDeclaration = "static " + fieldDeclaration;
    }
    fieldDeclaration = setInitialValueForVariableDeclaration(fieldTypeClassName, fieldDeclaration);
    classThatContainField.addFields(fieldDeclaration);
    classAndPackageMap.put(thisFieldType, packageName);
    classAndPackageMap.put(className, packageName);
    syntheticTypeAndClass.put(thisFieldType, classThatContainField);
    this.updateMissingClass(typeClass);
    this.updateMissingClass(classThatContainField);
  }

  /**
   * Based on the Map returned by JavaTypeCorrect, this method updates the types of methods in
   * synthetic classes.
   *
   * @param typeToCorrect the Map to be analyzed
   */
  public void updateTypes(Map<String, String> typeToCorrect) {
    for (String incorrectType : typeToCorrect.keySet()) {
      // update incorrecType if it is the type of a field in a synthetic class
      if (syntheticTypeAndClass.containsKey(incorrectType)) {
        UnsolvedClassOrInterface relatedClass = syntheticTypeAndClass.get(incorrectType);
        updateTypeForSyntheticClasses(
            relatedClass.getClassName(),
            relatedClass.getPackageName(),
            true,
            incorrectType,
            typeToCorrect.get(incorrectType));
        continue;
      }
      UnsolvedClassOrInterface relatedClass = syntheticMethodReturnTypeAndClass.get(incorrectType);
      if (relatedClass != null) {
        updateTypeForSyntheticClasses(
            relatedClass.getClassName(),
            relatedClass.getPackageName(),
            false,
            incorrectType,
            typeToCorrect.get(incorrectType));
      }
      // if the above condition is not met, then this incorrectType is a synthetic type for the
      // fields of the parent class rather than the return type of some methods
      else {
        for (UnsolvedClassOrInterface unsolClass : missingClass) {
          for (String parentClass : classAndItsParent.values()) {
            // TODO: should this also check that unsolClass's package name is
            // the correct one for the parent? Martin isn't sure how to do that here.
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
   * Based on the set returned by JavaTypeCorrect, this method corrects the Throwable extension for
   * synthetic classes as needed.
   *
   * @param typesToExtendThrowable the set of synthetic types that need Throwable extension.
   */
  public void updateTypesToExtendThrowable(Set<String> typesToExtendThrowable) {
    Set<UnsolvedClassOrInterface> modifiedClasses = new HashSet<>();

    for (String typeToExtendThrowable : typesToExtendThrowable) {
      Iterator<UnsolvedClassOrInterface> iterator = missingClass.iterator();
      while (iterator.hasNext()) {
        UnsolvedClassOrInterface missedClass = iterator.next();
        if (missedClass.getClassName().equals(typeToExtendThrowable)) {
          iterator.remove();
          missedClass.setThrowableToTrue();
          modifiedClasses.add(missedClass);
          this.deleteOldSyntheticClass(missedClass);
          this.createMissingClass(missedClass);
        }
      }
    }

    missingClass.addAll(modifiedClasses);
  }

  /**
   * Updates the types for fields or methods in a synthetic class.
   *
   * @param className The name of the synthetic class.
   * @param packageName The package of the synthetic class.
   * @param updateAField True if updating the type of a field, false to update the type of a method.
   * @param incorrectTypeName The name of the current incorrect type.
   * @param correctTypeName The name of the desired correct type.
   */
  public void updateTypeForSyntheticClasses(
      String className,
      String packageName,
      boolean updateAField,
      String incorrectTypeName,
      String correctTypeName) {
    UnsolvedClassOrInterface classToSearch = new UnsolvedClassOrInterface(className, packageName);
    Iterator<UnsolvedClassOrInterface> iterator = missingClass.iterator();
    while (iterator.hasNext()) {
      UnsolvedClassOrInterface missedClass = iterator.next();
      // Class comparison is based on class name and package name only.
      if (missedClass.equals(classToSearch)) {
        iterator.remove(); // Remove the outdated version of this synthetic class from the list
        if (updateAField) {
          missedClass.updateFieldByType(incorrectTypeName, correctTypeName);
        } else {
          missedClass.updateMethodByReturnType(incorrectTypeName, correctTypeName);
        }
        missingClass.add(missedClass); // Add the modified missedClass back to the list
        this.deleteOldSyntheticClass(missedClass);
        this.createMissingClass(missedClass);
        return;
      }
    }
    throw new RuntimeException("Could not find the corresponding missing class!");
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

  /**
   * This indirection is here to make it easier to debug infinite loops. Never set gotException
   * directly, but instead call this function.
   */
  private void gotException() {
    if (DEBUG) {
      StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
      System.out.println("setting gotException to true from: " + stackTraceElements[2]);
    }
    this.gotException = true;
  }
}
