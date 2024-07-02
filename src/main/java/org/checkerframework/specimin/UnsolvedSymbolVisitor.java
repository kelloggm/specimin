package org.checkerframework.specimin;

import com.github.javaparser.StaticJavaParser;
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
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.WildcardType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.checker.signature.qual.ClassGetSimpleName;
import org.checkerframework.checker.signature.qual.DotSeparatedIdentifiers;
import org.checkerframework.checker.signature.qual.FullyQualifiedName;

/**
 * The visitor for the preliminary phase of Specimin. This visitor goes through the input files,
 * notices all the methods, fields, and types belonging to classes not in the source codes, and
 * creates synthetic versions of those symbols. This preliminary step helps to prevent
 * UnsolvedSymbolException errors for the next phases.
 *
 * <p>Note: To comprehend this visitor quickly, it is recommended to start by reading all the visit
 * methods.
 */
public class UnsolvedSymbolVisitor extends ModifierVisitor<Void> {

  /**
   * Flag for whether or not to print debugging output. Should always be false except when you are
   * actively debugging.
   */
  private static final boolean DEBUG = false;

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

  /** The symbol table for type variables. A type variable is mapped to the list of its bounds. */
  private final ArrayDeque<Map<String, NodeList<ClassOrInterfaceType>>> typeVariables =
      new ArrayDeque<>();

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

  /**
   * List of fully-qualified names of classes that are directly imported (i.e., without the use of a
   * wildcard import statement.)
   */
  private List<String> importStatement = new ArrayList<>();

  /** The packages that were imported via wildcard ("*") imports. */
  private final List<String> wildcardImports = new ArrayList<>(1);

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
   * The fully-qualified name of each Java class in the original codebase mapped to the
   * corresponding Java file.
   */
  private Map<String, Path> existingClassesToFilePath;

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

  /**
   * List of signatures of target methods as specified by users. All signatures have spaces removed
   * for ease of comparison.
   */
  private final Set<String> targetMethodsSignatures;

  /** List of signatures of target fields as specified by users. */
  private final Set<String> targetFieldsSignatures;

  /**
   * Fields and methods that could be called inside the target methods. We call them potential-used
   * because the usage check is simply based on the simple names of those members.
   */
  private final Set<String> potentialUsedMembers = new HashSet<>();

  /**
   * Check whether the visitor is inside the declaration of a target method or field. Symbols inside
   * the declarations of target members will be solved if they have one of the following types:
   * ClassOrInterfaceType, Parameters, VariableDeclarator, MethodCallExpr, FieldAccessExpr,
   * ExplicitConstructorInvocationStmt, NameExpr, MethodDeclaration, and ObjectCreationExpr.
   */
  private boolean insideTargetMember = false;

  /**
   * Check whether the visitor is inside the declaration of a member that could be used by the
   * target methods. Symbols inside the declarations of potentially-used members will be solved if
   * they have one of the following types: ClassOrInterfaceType, Parameters, and VariableDeclarator.
   */
  private boolean insidePotentialUsedMember = false;

  /** The qualified name of the current class. */
  private String currentClassQualifiedName = "";

  /**
   * Indicating whether the visitor is currently visiting the parameter part of a catch block (i.e.,
   * the "(...)" segment within a catch(...){...} clause).
   */
  private boolean isInsideCatchBlockParameter = false;

  /**
   * Create a new UnsolvedSymbolVisitor instance
   *
   * @param rootDirectory the root directory of the input files
   * @param existingClassesToFilePath The fully-qualified name of each Java class in the original
   *     codebase mapped to the corresponding Java file.
   * @param targetMethodsSignatures the list of signatures of target methods as specified by the
   *     user.
   * @param targetFieldsSignature the list of signatures of target fields as specified by the user.
   */
  public UnsolvedSymbolVisitor(
      String rootDirectory,
      Map<String, Path> existingClassesToFilePath,
      List<String> targetMethodsSignatures,
      List<String> targetFieldsSignature) {
    this.rootDirectory = rootDirectory;
    this.gotException = true;
    this.existingClassesToFilePath = existingClassesToFilePath;
    this.targetMethodsSignatures = new HashSet<>();
    for (String methodSignature : targetMethodsSignatures) {
      this.targetMethodsSignatures.add(methodSignature.replaceAll("\\s", ""));
    }
    this.targetFieldsSignatures = new HashSet<>();
    this.targetFieldsSignatures.addAll(targetFieldsSignature);
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
        if (!"*".equals(className)) {
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
   * Get the names of members that could be used by the target methods.
   *
   * @return a copy of potentialUsedMembers.
   */
  public Set<String> getPotentialUsedMembers() {
    Set<String> copyOfPotentialUsedMembers = new HashSet<>();
    copyOfPotentialUsedMembers.addAll(potentialUsedMembers);
    return copyOfPotentialUsedMembers;
  }

  /**
   * Return the set of synthetic classes created by the UnsolvedSymbolVisitor in the form of a set
   * of strings.
   *
   * @return the set of created synthetic classes represented as a set of strings.
   */
  public Set<String> getSyntheticClassesAsAStringSet() {
    Set<String> syntheticClassesAsString = new HashSet<>();
    for (UnsolvedClassOrInterface syntheticClass : missingClass) {
      syntheticClassesAsString.add(syntheticClass.toString());
    }
    return syntheticClassesAsString;
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
   * @return a copy of addedTargetFiles.
   */
  public Set<String> getAddedTargetFiles() {
    Set<String> copyOfTargetFiles = new HashSet<>();
    copyOfTargetFiles.addAll(addedTargetFiles);
    return copyOfTargetFiles;
  }

  @Override
  public Node visit(ImportDeclaration decl, Void arg) {
    /*
     * This method visits an import declaration in the currently visiting CompilationUnit and update the content of wildCardImports and staticImportedMembersMap accordingly.
     */

    if (decl.isAsterisk()) {
      wildcardImports.add(decl.getNameAsString());
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
    processAnnotations(node.getAnnotations());
    return super.visit(node, arg);
  }

  /**
   * Maintains the data structures of this class (like the {@link #className}, {@link
   * #currentClassQualifiedName}, {@link #addedTargetFiles}, etc.) based on a class, interface, or
   * enum declaration. Call this method before calling super.visit().
   *
   * @param decl the class, interface, or enum declaration
   */
  private void maintainDataStructuresPreSuper(TypeDeclaration<?> decl) {
    SimpleName nodeName = decl.getName();
    className = nodeName.asString();
    if (decl.isNestedType()) {
      this.currentClassQualifiedName += "." + decl.getName().asString();
    } else if (!JavaParserUtil.isLocalClassDecl(decl)) {
      // the purpose of keeping track of class name is to recognize the signatures of target
      // methods. Since we don't take methods inside local classes as target methods, we don't need
      // to keep track of class name in this case.
      this.currentClassQualifiedName = decl.getFullyQualifiedName().orElseThrow();
    }
    if (decl.isEnumDeclaration()) {
      // Enums cannot extend other classes (they always extend Enum) and cannot have type
      // parameters, o it's not necessary to do any maintenance on the data structures that
      // track superclasses or type parameters in the enum case (only implemented interfaces).
      NodeList<ClassOrInterfaceType> implementedTypes =
          decl.asEnumDeclaration().getImplementedTypes();
      updateForExtendedAndImplementedTypes(implementedTypes, implementedTypes, false);
    } else if (decl.isClassOrInterfaceDeclaration()) {
      ClassOrInterfaceDeclaration asClassOrInterface = decl.asClassOrInterfaceDeclaration();

      // Maintenance of type parameters
      addTypeVariableScope(asClassOrInterface.getTypeParameters());

      // Maintenance of superclasses and implemented/extended classes.
      if (asClassOrInterface.getExtendedTypes().isNonEmpty()) {
        // note that since Specimin does not have access to the classpaths of the project, all the
        // unsolved methods related to inheritance will be placed in the parent class, even if there
        // is a grandparent class and so forth.
        SimpleName superClassSimpleName = asClassOrInterface.getExtendedTypes().get(0).getName();
        classAndItsParent.put(className, superClassSimpleName.asString());
      }
      NodeList<ClassOrInterfaceType> implementedTypes = asClassOrInterface.getImplementedTypes();
      // Not sure why getExtendedTypes return a list, since a class can only extends at most one
      // class in Java.
      NodeList<ClassOrInterfaceType> extendedAndImplementedTypes =
          asClassOrInterface.getExtendedTypes();
      extendedAndImplementedTypes.addAll(implementedTypes);
      updateForExtendedAndImplementedTypes(
          extendedAndImplementedTypes, implementedTypes, asClassOrInterface.isInterface());
    } else {
      throw new RuntimeException(
          "unexpected type of declaration; expected a class, interface, or enum: " + decl);
    }
    declaredMethod.addFirst(new HashSet<>(decl.getMethods()));
  }

  /**
   * Maintains the data structures of this class (like the {@link #className}, {@link
   * #currentClassQualifiedName}, {@link #addedTargetFiles}, etc.) based on a class, interface, or
   * enum declaration. Call this method after calling super.visit().
   *
   * @param decl the class, interface, or enum declaration
   */
  private void maintainDataStructuresPostSuper(TypeDeclaration<?> decl) {
    if (decl.isClassOrInterfaceDeclaration()) {
      // Enums don't have type variables, so no scope for them is created
      // when entering an enum.
      typeVariables.removeFirst();
    }

    declaredMethod.removeFirst();
    if (decl.isNestedType()) {
      this.currentClassQualifiedName =
          this.currentClassQualifiedName.substring(
              0, this.currentClassQualifiedName.lastIndexOf('.'));
    } else if (!JavaParserUtil.isLocalClassDecl(decl)) {
      this.currentClassQualifiedName = "";
    }
  }

  @Override
  public Visitable visit(EnumDeclaration node, Void arg) {
    maintainDataStructuresPreSuper(node);
    Visitable result = super.visit(node, arg);
    maintainDataStructuresPostSuper(node);
    processAnnotations(node.getAnnotations());
    return result;
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration node, Void arg) {
    maintainDataStructuresPreSuper(node);
    Visitable result = super.visit(node, arg);
    maintainDataStructuresPostSuper(node);
    processAnnotations(node.getAnnotations());
    return result;
  }

  /**
   * Updates the list of classes/interfaces to keep based on the extends/implements clauses of a
   * class, interface, or enum. Does not side effect its arguments, so it's safe to pass the same
   * value for the first two arguments (e.g., if this is an enum, which cannot extend anything).
   *
   * @param extendedAndImplementedTypes the list of extended and implemented classes/interfaces
   * @param implementedTypes the list of implemented interfaces
   * @param isAnInterface is the node whose extends/implements clauses are being considered an
   *     interface
   */
  private void updateForExtendedAndImplementedTypes(
      NodeList<ClassOrInterfaceType> extendedAndImplementedTypes,
      NodeList<ClassOrInterfaceType> implementedTypes,
      boolean isAnInterface) {
    for (ClassOrInterfaceType implementedOrExtended : extendedAndImplementedTypes) {
      String qualifiedName = getQualifiedNameForClassOrInterfaceType(implementedOrExtended);
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
        try {
          implementedOrExtended.resolve();
          continue;
        }
        // IllegalArgumentException is thrown when implementedOrExtended has a generic type.
        catch (UnsolvedSymbolException | IllegalArgumentException e) {
          // this extended/implemented type is an interface if it is in the declaration of an
          // interface, or if it is used with the "implements" keyword.
          boolean typeIsAnInterface =
              isAnInterface || implementedTypes.contains(implementedOrExtended);
          if (typeIsAnInterface) {
            solveSymbolsForClassOrInterfaceType(implementedOrExtended, true);
            @SuppressWarnings(
                "signature") // an empty array list is not a list of @ClassGetSimpleName, but since
            // we will add typeName to that list right after the initialization,
            // this code is correct.
            List<@ClassGetSimpleName String> interfaceName =
                classToItsUnsolvedInterface.computeIfAbsent(className, k -> new ArrayList<>());
            interfaceName.add(implementedOrExtended.getName().asString());
          } else {
            solveSymbolsForClassOrInterfaceType(implementedOrExtended, false);
          }
        }
      }
    }
  }

  @Override
  public Visitable visit(ExplicitConstructorInvocationStmt node, Void arg) {
    /*
     * This methods create synthetic classes for unsolved explicit constructor invocation, such as super(). We only solve the invocation after all of its arguments have been solved.
     */
    if (node.isThis()) {
      return super.visit(node, arg);
    }
    if (!insideTargetMember) {
      return super.visit(node, arg);
    }
    if (!canSolveArguments(node.getArguments())) {
      // wait for the next run of UnsolvedSymbolVisitor
      return super.visit(node, arg);
    }

    try {
      // check if the symbol is solvable. If it is, then there's no need to create a synthetic file.
      node.resolve().getQualifiedSignature();
      return super.visit(node, arg);
    } catch (Exception e) {
      NodeList<Expression> arguments = node.getArguments();
      String pkgName = getPackageFromClassName(getParentClass(className));
      List<String> argList = getArgumentTypesImpl(arguments, pkgName);
      UnsolvedMethod constructorMethod = new UnsolvedMethod(getParentClass(className), "", argList);
      // if the parent class can not be found in the import statements, Specimin assumes it is in
      // the same package as the child class.
      UnsolvedClassOrInterface superClass =
          new UnsolvedClassOrInterface(getParentClass(className), pkgName);
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
    /*
     * This method is a copy from the original visit(IfStmt, Void) from JavaParser. We add additional codes here to update the set of local variables.
     */
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
  public Visitable visit(ForEachStmt node, Void p) {
    HashSet<String> currentLocalVariables = new HashSet<>();
    localVariables.addFirst(currentLocalVariables);
    String loopVarName = node.getVariableDeclarator().getNameAsString();
    currentLocalVariables.add(loopVarName);
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
  @SuppressWarnings("nullness")
  // This method returns a nullable result, and "comment" can be null for the phrase
  // node.setComment(comment).
  // These are the codes from JavaParser, so we optimistically assume that these lines are safe.
  public Visitable visit(CatchClause node, Void arg) {
    /*
     * This method is a copy from the visit(CatchClause, Void) method of JavaParser. We extend it to update the set of local variables and the flag isInsideCatchBlockParameter
     */
    HashSet<String> currentLocalVariables = new HashSet<>();
    currentLocalVariables.add(node.getParameter().getNameAsString());
    localVariables.addFirst(currentLocalVariables);
    BlockStmt body = (BlockStmt) node.getBody().accept(this, arg);
    // There can not be a parameter list inside a parameter list, hence we don't need a temporary
    // local variable like in the case of insideTargetMethod.
    isInsideCatchBlockParameter = true;
    Parameter parameter = (Parameter) node.getParameter().accept(this, arg);
    isInsideCatchBlockParameter = false;
    Comment comment = node.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
    if (body == null || parameter == null) {
      localVariables.removeFirst();
      return null;
    }
    node.setBody(body);
    node.setParameter(parameter);
    node.setComment(comment);
    localVariables.removeFirst();
    return node;
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
  public Visitable visit(InstanceOfExpr node, Void p) {
    // If we have x : X and x instanceof Y, then X must be a supertype
    // of Y if X != Y. The JLS says (15.20.2): "If a cast of the RelationalExpression to the
    // ReferenceType would be rejected as a compile-time error, then the instanceof relational
    // expression likewise produces a compile-time error. In such a situation, the result of the
    // instanceof expression could never be true."
    //
    // This visit method uses this fact to add extends clauses to classes created by
    // UnsolvedSymbolVisitor.
    ReferenceType referenceType;
    if (node.getPattern().isPresent()) {
      PatternExpr patternExpr = node.getPattern().get();
      referenceType = patternExpr.getType();
    } else {
      referenceType = node.getType();
    }
    Expression relationalExpr = node.getExpression();
    String relationalExprFQN, referenceTypeFQN;
    try {
      referenceTypeFQN = referenceType.resolve().describe();
      relationalExprFQN = relationalExpr.calculateResolvedType().describe();
    } catch (UnsolvedSymbolException e) {
      // Try again next time.
      this.gotException();
      return super.visit(node, p);
    }

    if (referenceTypeFQN.equals(relationalExprFQN)) {
      // A type can't extend itself.
      return super.visit(node, p);
    }

    for (UnsolvedClassOrInterface syntheticClass : missingClass) {
      if (syntheticClass.getQualifiedClassName().equals(referenceTypeFQN)) {
        // TODO: check for double extends?
        syntheticClass.extend(relationalExprFQN);
        break;
      }
    }

    return super.visit(node, p);
  }

  @Override
  public Visitable visit(LambdaExpr node, Void p) {
    boolean noLocalScope = localVariables.isEmpty();
    if (noLocalScope) {
      localVariables.addFirst(new HashSet<>());
    }
    // add the parameters to the local variable map
    // Note that lambdas DO NOT CREATE A NEW SCOPE
    // (why? ask whoever designed the feature...)
    for (Parameter lambdaParam : node.getParameters()) {
      localVariables.getFirst().add(lambdaParam.getNameAsString());
      processAnnotations(lambdaParam.getAnnotations());
    }

    Visitable result = super.visit(node, p);

    // then remove them
    if (noLocalScope) {
      localVariables.removeFirst();
    } else {
      for (Parameter lambdaParam : node.getParameters()) {
        localVariables.getFirst().remove(lambdaParam.getNameAsString());
      }
    }
    return result;
  }

  @Override
  public Visitable visit(VariableDeclarator decl, Void p) {
    System.out.println(decl);
    boolean oldInsidePotentialUsedMember = insidePotentialUsedMember;
    // This part is to update the symbol table.
    boolean isAField =
        decl.getParentNode().isPresent()
            && (decl.getParentNode().get() instanceof FieldDeclaration);
    if (!isAField) {
      Set<String> currentListOfLocals = localVariables.peek();
      if (currentListOfLocals == null) {
        throw new RuntimeException("tried to add a variable without a scope available: " + decl);
      }
      currentListOfLocals.add(decl.getNameAsString());
    }
    if (potentialUsedMembers.contains(decl.getName().asString())) {
      insidePotentialUsedMember = true;
    }
    if (!insideTargetMember && !insidePotentialUsedMember) {
      return super.visit(decl, p);
    }

    // This part is to create synthetic class for the type of decl if needed.
    Type declType = decl.getType();
    if (declType.isVarType()) {
      // nothing to do here. A var type could never be solved.
      Visitable result = super.visit(decl, p);
      insidePotentialUsedMember = oldInsidePotentialUsedMember;
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
        int typeParamIndex = typeAsString.indexOf('<');
        int typeParamCount = -1;
        if (typeParamIndex != -1) {
          ClassOrInterfaceType asType = StaticJavaParser.parseClassOrInterfaceType(typeAsString);
          typeParamCount = asType.getTypeArguments().get().size();
          typeAsString = typeAsString.substring(0, typeParamIndex);
        }

        @SuppressWarnings(
            "signature") // since this type is in a fully-qualified form, or we make it
        // fully-qualified
        @FullyQualifiedName String qualifiedTypeName =
            typeAsString.contains(".")
                ? typeAsString
                : getPackageFromClassName(typeAsString) + "." + typeAsString;
        UnsolvedClassOrInterface unsolved =
            getSimpleSyntheticClassFromFullyQualifiedName(qualifiedTypeName);
        if (typeParamCount != -1) {
          unsolved.setNumberOfTypeVariables(typeParamCount);
        }
        updateMissingClass(unsolved);
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
        String packageName = getPackageFromClassName(className);
        UnsolvedClassOrInterface newClass = new UnsolvedClassOrInterface(className, packageName);
        updateMissingClass(newClass);
      }
    }
    Visitable result = super.visit(decl, p);
    insidePotentialUsedMember = oldInsidePotentialUsedMember;
    return result;
  }

  @Override
  public Visitable visit(NameExpr node, Void arg) {
    if (!insideTargetMember) {
      return super.visit(node, arg);
    }
    String name = node.getNameAsString();
    if (fieldNameToClassNameMap.containsKey(name)) {
      potentialUsedMembers.add(name);
      if (!canBeSolved(node)) {
        gotException();
      } else {
        // check if all the type parameters are resolved.
        ResolvedType nameExprType = node.resolve().getType();
        if (nameExprType.isReferenceType()) {
          ResolvedReferenceType nameExprReferenceType = nameExprType.asReferenceType();
          nameExprReferenceType.getAllAncestors();
          if (!hasResolvedTypeParameters(nameExprReferenceType)) {
            gotException();
          }
        }
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
    processAnnotations(node.getAnnotations());
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

      if (targetFieldsSignatures.contains(
          currentClassQualifiedName + "#" + var.getNameAsString())) {
        boolean oldInsideTargetMember = insideTargetMember;
        insideTargetMember = true;
        Visitable result = super.visit(node, arg);
        insideTargetMember = oldInsideTargetMember;
        return result;
      }
    }
    return super.visit(node, arg);
  }

  @Override
  public Visitable visit(ConstructorDeclaration node, Void arg) {
    String methodQualifiedSignature =
        this.currentClassQualifiedName
            + "#"
            + TargetMethodFinderVisitor.removeMethodReturnTypeAndAnnotations(
                node.getDeclarationAsString(false, false, false));
    boolean oldInsideTargetMember = insideTargetMember;
    if (targetMethodsSignatures.contains(methodQualifiedSignature.replace("\\s", ""))) {
      insideTargetMember = true;
    }
    boolean oldInsidePotentialUsedMember = insidePotentialUsedMember;
    if (potentialUsedMembers.contains(node.getNameAsString())) {
      insidePotentialUsedMember = true;
    }
    addTypeVariableScope(node.getTypeParameters());
    Visitable result = super.visit(node, arg);
    typeVariables.removeFirst();
    insideTargetMember = oldInsideTargetMember;
    insidePotentialUsedMember = oldInsidePotentialUsedMember;
    processAnnotations(node.getAnnotations());
    return result;
  }

  @SuppressWarnings(
      "nullness:return") // return type is not used, and we need to avoid calling super.visit()
  @Override
  public Visitable visit(MethodDeclaration node, Void arg) {
    String methodQualifiedSignature =
        this.currentClassQualifiedName
            + "#"
            + TargetMethodFinderVisitor.removeMethodReturnTypeAndAnnotations(
                node.getDeclarationAsString(false, false, false));
    String methodSimpleName = node.getName().asString();
    // Annotations are handled by processMethodDeclaration
    if (targetMethodsSignatures.contains(methodQualifiedSignature.replaceAll("\\s", ""))) {
      boolean oldInsideTargetMember = insideTargetMember;
      insideTargetMember = true;
      Visitable result = processMethodDeclaration(node);
      insideTargetMember = oldInsideTargetMember;
      return result;
    } else if (potentialUsedMembers.contains(methodSimpleName)) {
      boolean oldInsidePotentialUsedMember = insidePotentialUsedMember;
      insidePotentialUsedMember = true;
      Visitable result = processMethodDeclaration(node);
      insidePotentialUsedMember = oldInsidePotentialUsedMember;
      return result;
    } else if (insideTargetMember) {
      return processMethodDeclaration(node);
    } else {
      // Do not call super.visit(): this method is definitely unused by the targets, and so
      // there's no reason to solve its symbols. Furthermore, doing so may lead to data
      // structure corruption (e.g., of type variables), since processMethodDeclaration,
      // which does data structure management, will not be called.
      return null;
    }
  }

  @Override
  public Visitable visit(FieldAccessExpr node, Void p) {
    if (!insideTargetMember) {
      return super.visit(node, p);
    }
    potentialUsedMembers.add(node.getNameAsString());
    boolean canBeSolved = canBeSolved(node);
    if (isASuperCall(node) && !canBeSolved) {
      updateSyntheticClassForSuperCall(node);
    } else if (updatedAddedTargetFilesForPotentialEnum(node)) {
      return super.visit(node, p);
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
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      // for a qualified name field access such as org.sample.MyClass.field, org.sample will also be
      // considered FieldAccessExpr.
      if (isAClassPath(node.getScope().toString())) {
        gotException();
      }
    }
    return super.visit(node, p);
  }

  @Override
  public Visitable visit(MethodReferenceExpr node, Void p) {
    if (insideTargetMember) {
      // TODO: handle all of the possible forms listed in JLS 15.13, not just the simplest
      Expression scope = node.getScope();
      if (scope.isTypeExpr()) {
        Type scopeAsType = scope.asTypeExpr().getType();
        String scopeAsTypeFQN = scopeAsType.asString();
        if (!isAClassPath(scopeAsTypeFQN) && scopeAsType.isClassOrInterfaceType()) {
          scopeAsTypeFQN =
              getQualifiedNameForClassOrInterfaceType(scopeAsType.asClassOrInterfaceType());
        }
        if (classfileIsInOriginalCodebase(scopeAsTypeFQN)) {
          addedTargetFiles.add(qualifiedNameToFilePath(scopeAsTypeFQN));
        } else {
          // TODO: create a synthetic class?
        }
      }
      String identifier = node.getIdentifier();
      // can be either the name of a method or "new"
      if ("new".equals(identifier)) {
        // TODO: figure out how to handle this case
        System.err.println("Specimin warning: new in method references is not supported: " + node);
        return super.visit(node, p);
      }
      potentialUsedMembers.add(identifier);
    }
    return super.visit(node, p);
  }

  @Override
  public Visitable visit(MethodCallExpr method, Void p) {
    /*
     * There's a specific order in which we resolve symbols for a method call.
     * We ensure that the caller and its parameters are resolved before solving the method itself.
     * For instance, in a method call like a.b(c, d, e,...), we solve a, c, d, e,... before resolving b.
     */
    if (!insideTargetMember) {
      return super.visit(method, p);
    }
    potentialUsedMembers.add(method.getName().asString());
    if (canBeSolved(method) && isFromAJarFile(method)) {
      updateClassesFromJarSourcesForMethodCall(method);
      return super.visit(method, p);
    }
    // we will wait for the next run to solve this method call
    if (!canSolveArguments(method.getArguments())) {
      return super.visit(method, p);
    }
    if (isASuperCall(method) && !canBeSolved(method)) {
      updateSyntheticClassForSuperCall(method);
      return super.visit(method, p);
    }
    String methodName = method.getNameAsString();
    if (isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method)) {
      updateClassSetWithStaticMethodCall(method);
    } else if (unsolvedAndCalledByASimpleClassName(method)) {
      updateClassSetWithStaticMethodCall(method);
    } else if (calledByAnIncompleteClass(method)) {
      /*
       * Note that the body here assumes that the method is not static. This assumption is safe since we have isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method) and unsolvedAndCalledByASimpleClassName(method) before this condition.
       */
      String qualifiedNameOfIncompleteClass = getIncompleteClass(method);
      if (classfileIsInOriginalCodebase(qualifiedNameOfIncompleteClass)) {
        addedTargetFiles.add(qualifiedNameToFilePath(qualifiedNameOfIncompleteClass));
      } else {
        updateUnsolvedClassOrInterfaceWithMethod(method, qualifiedNameOfIncompleteClass, "", false);
      }
    } else if (staticImportedMembersMap.containsKey(methodName)) {
      @FullyQualifiedName String className = staticImportedMembersMap.get(methodName);
      String methodFullyQualifiedCall = className + "." + methodName;
      String pkgName = className.substring(0, className.lastIndexOf('.'));
      // everything inside the (...) will be trimmed
      updateClassSetWithQualifiedStaticMethodCall(
          methodFullyQualifiedCall + "()", getArgumentTypesFromMethodCall(method, pkgName));
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
    if (!canBeSolved(method)) {
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
  public Visitable visit(EnumConstantDeclaration expr, Void p) {
    // this is a bit hacky, but we don't remove any enum constant declarations if they are ever
    // used, so it's safer to just preserve anything that they use by pretending that we're inside a
    // target method.
    boolean oldInsideTargetMember = insideTargetMember;
    insideTargetMember = true;
    Visitable result = super.visit(expr, p);
    insideTargetMember = oldInsideTargetMember;
    processAnnotations(expr.getAnnotations());
    return result;
  }

  @Override
  public Visitable visit(ClassOrInterfaceType typeExpr, Void p) {
    processAnnotations(typeExpr.getAnnotations());
    // Workaround for a JavaParser bug: When a type is referenced using its fully-qualified name,
    // like com.example.Dog dog, JavaParser considers its package components (com and com.example)
    // as types, too. This issue happens even when the source file of the Dog class is present in
    // the codebase.
    if (!isCapital(typeExpr.getName().asString())) {
      return super.visit(typeExpr, p);
    }
    // type belonging to a class declaration will be handled by the visit method for
    // ClassOrInterfaceDeclaration
    if (typeExpr.getParentNode().get() instanceof ClassOrInterfaceDeclaration) {
      return super.visit(typeExpr, p);
    }
    if (!insideTargetMember && !insidePotentialUsedMember) {
      return super.visit(typeExpr, p);
    }
    resolveTypeExpr(typeExpr);

    return super.visit(typeExpr, p);
  }

  @Override
  public Visitable visit(WildcardType type, Void p) {
    if (!insideTargetMember && !insidePotentialUsedMember) {
      return super.visit(type, p);
    }
    resolveTypeExpr(type);
    return super.visit(type, p);
  }

  @Override
  public Visitable visit(ArrayType type, Void p) {
    if (!insideTargetMember && !insidePotentialUsedMember) {
      return super.visit(type, p);
    }
    resolveTypeExpr(type);
    return super.visit(type, p);
  }

  /**
   * Shared logic for checking whether type expressions (e.g., ArrayType, ClassOrInterfaceType,
   * etc.) are resolvable, and creating synthetic classes if not.
   *
   * @param type a type expression
   */
  private void resolveTypeExpr(Type type) {
    if (type.isArrayType()) {
      resolveTypeExpr(type.asArrayType().getComponentType());
      return;
    }

    if (type.isWildcardType()) {
      Optional<ReferenceType> extended = type.asWildcardType().getExtendedType();
      if (extended.isPresent()) {
        resolveTypeExpr(extended.get());
      }
      Optional<ReferenceType> sup = type.asWildcardType().getSuperType();
      if (sup.isPresent()) {
        resolveTypeExpr(sup.get());
      }
      return;
    }

    if (!type.isClassOrInterfaceType()) {
      return;
    }
    ClassOrInterfaceType typeExpr = type.asClassOrInterfaceType();

    if (isTypeVar(typeExpr.getName().asString())) {
      updateSyntheticClassesForTypeVar(typeExpr);
      return;
    }
    if (updateTargetFilesListForExistingClassWithInheritance(typeExpr)) {
      return;
    }
    try {
      // resolve() checks whether this type is resolved. getAllAncestor() checks whether this type
      // extends or implements a resolved class/interface.
      JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(typeExpr).getAllAncestors();
      return;
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
        return;
      }

      // below is for other three cases.

      // This method only updates type variables for unsolved classes. Other problems causing a
      // class to be unsolved will be fixed by other methods.
      String typeRawName = typeExpr.getElementType().asString();
      if (typeExpr.isClassOrInterfaceType()
          && typeExpr.asClassOrInterfaceType().getTypeArguments().isPresent()) {
        // remove type arguments
        typeRawName = typeRawName.substring(0, typeRawName.indexOf("<"));
      }

      if (isTypeVar(typeRawName)) {
        // If the type name itself is an in-scope type variable, just return without attempting
        // to create a missing class.
        return;
      }
      solveSymbolsForClassOrInterfaceType(typeExpr, false);
      gotException();
    }
  }

  @Override
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    String oldClassName = className;
    if (!insideTargetMember) {
      if (newExpr.getAnonymousClassBody().isPresent()) {
        // Need to do data structure maintenance
        className = newExpr.getType().getName().asString();
      }
      Visitable result = super.visit(newExpr, p);
      className = oldClassName;
      return result;
    }
    potentialUsedMembers.add(newExpr.getTypeAsString());
    // Cannot be newExpr.getTypeAsString(), because that will include type variables,
    // which is undesirable.
    String type = newExpr.getType().getNameAsString();
    if (canBeSolved(newExpr)) {
      if (isFromAJarFile(newExpr)) {
        updateClassesFromJarSourcesForObjectCreation(newExpr);
      }
      if (newExpr.getAnonymousClassBody().isPresent()) {
        // Need to do data structure maintenance
        className = newExpr.getType().getName().asString();
      }
      Visitable result = super.visit(newExpr, p);
      className = oldClassName;
      return result;
    }
    gotException();
    /*
     * For an unresolved object creation, the arguments are resolved first before the expression itself is resolved.
     */
    try {
      List<String> argumentsCreation =
          getArgumentTypesFromObjectCreation(newExpr, getPackageFromClassName(type));
      UnsolvedMethod creationMethod = new UnsolvedMethod("", type, argumentsCreation);
      updateUnsolvedClassWithClassName(type, false, false, creationMethod);
    } catch (Exception q) {
      // The exception originates from the call to getArgumentTypesFromObjectCreation within the try
      // block, indicating unresolved parameters in this object creation.
      gotException();
    }
    if (newExpr.getAnonymousClassBody().isPresent()) {
      // Need to do data structure maintenance
      className = newExpr.getType().getName().asString();
    }
    Visitable result = super.visit(newExpr, p);
    className = oldClassName;
    return result;
  }

  /**
   * Converts a qualified class name into a relative file path. Angle brackets for type variables
   * are permitted in the input.
   *
   * @param qualifiedName The qualified name of the class.
   * @return The relative file path corresponding to the qualified name.
   */
  public String qualifiedNameToFilePath(String qualifiedName) {
    if (!existingClassesToFilePath.containsKey(qualifiedName)) {
      throw new RuntimeException(
          "qualifiedNameToFilePath only works for classes in the original directory");
    }
    Path absoluteFilePath = existingClassesToFilePath.get(qualifiedName);
    // theoretically rootDirectory should already be absolute as stated in README.
    Path absoluteRootDirectory = Paths.get(rootDirectory).toAbsolutePath();
    return absoluteRootDirectory.relativize(absoluteFilePath).toString();
  }

  /**
   * Updates the list of added target files based on a FieldAccessExpr if it represents an enum
   * constant.
   *
   * @param expr the FieldAccessExpr potentially representing an Enum constant.
   * @return true if the update was successful, false otherwise.
   */
  public boolean updatedAddedTargetFilesForPotentialEnum(FieldAccessExpr expr) {
    ResolvedValueDeclaration resolved;
    try {
      resolved = expr.resolve();
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      return false;
    }
    if (resolved.isEnumConstant()) {
      String filePathName = qualifiedNameToFilePath(resolved.getType().describe());
      if (!addedTargetFiles.contains(filePathName)) {
        gotException();
        addedTargetFiles.add(filePathName);
        return true;
      }
    }
    return false;
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
        List<String> methodTypesOfArguments = getArgumentTypesFromMethodCall(method, null);
        NodeList<Parameter> methodDeclaredParameters = methodDeclared.getParameters();
        List<String> methodDeclaredTypesOfParameters = new ArrayList<>();
        for (Parameter parameter : methodDeclaredParameters) {
          try {
            if (isTypeVar(parameter.getTypeAsString())) {
              methodDeclaredTypesOfParameters.add(parameter.getTypeAsString());
            } else {
              ResolvedType parameterTypeResolved = parameter.getType().resolve();
              if (parameterTypeResolved.isPrimitive()) {
                methodDeclaredTypesOfParameters.add(parameterTypeResolved.asPrimitive().name());
              } else if (parameterTypeResolved.isReferenceType()) {
                methodDeclaredTypesOfParameters.add(
                    parameterTypeResolved.asReferenceType().getQualifiedName());
              }
            }
          } catch (UnsolvedSymbolException e) {
            // UnsolvedSymbolVisitor will not create any synthetic class at this iteration.
            return false;
          }
        }
        if (methodDeclaredTypesOfParameters.equals(methodTypesOfArguments)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Resolves symbols for a given ClassOrInterfaceType instance, including its type variables if
   * present.
   *
   * @param typeExpr The ClassOrInterfaceType instance to resolve symbols for.
   */
  private void solveSymbolsForClassOrInterfaceType(
      ClassOrInterfaceType typeExpr, boolean isAnInterface) {
    Optional<NodeList<Type>> typeArguments = typeExpr.getTypeArguments();
    UnsolvedClassOrInterface classToUpdate;
    int numberOfArguments = 0;
    String typeRawName = typeExpr.getElementType().asString();
    Set<String> preferredTypeVariables = new HashSet<>();
    if (typeArguments.isPresent()) {
      numberOfArguments = typeArguments.get().size();
      for (Type typeArgument : typeArguments.get()) {
        String typeArgStandardForm = typeArgument.toString();
        if (typeArgStandardForm.contains("@")) {
          // Remove annotations
          List<String> split = List.of(typeArgStandardForm.split("\\s"));
          typeArgStandardForm =
              split.stream().filter(s -> !s.startsWith("@")).collect(Collectors.joining(" "));
        }
        if (typeArgStandardForm.startsWith("? extends ")) {
          // there are 10 characters in "? extends ". The idea here is that users sometimes need
          // to add a wildcard to annotate a typevar - so "V" might be expressed as "@X ? extends
          // V".
          typeArgStandardForm = typeArgStandardForm.substring(10);
        }
        if (isTypeVar(typeArgStandardForm)) {
          preferredTypeVariables.add(typeArgStandardForm);
        } else if (typeArgument.isClassOrInterfaceType()) {
          // If the type argument is not a type variable, then
          // it must be a class/interface/etc. Try solving for it.
          // If that fails, create a synthetic class, just as we
          // would for something directly extended.
          try {
            typeArgument.resolve();
          } catch (UnsolvedSymbolException e) {
            // Assumption: type arguments are not interfaces. This isn't really true, but
            // Specimin doesn't have a way to know because the type argument context doesn't
            // tell us if this type is an interface or not.
            solveSymbolsForClassOrInterfaceType(typeArgument.asClassOrInterfaceType(), false);
          }
        }
      }
      if (!preferredTypeVariables.isEmpty() && preferredTypeVariables.size() != numberOfArguments) {
        throw new RuntimeException(
            "Numbers of type variables are not matching! "
                + preferredTypeVariables
                + " but expected "
                + numberOfArguments
                + " because the type arguments are: "
                + typeArguments.get()
                + " and the in-scope type variables are: "
                + typeVariables);
      }
      // without any type argument
      typeRawName = typeRawName.substring(0, typeRawName.indexOf("<"));
    }

    String packageName, className;
    if (isAClassPath(typeRawName)) {
      // Two cases: this could be either an Outer.Inner pair or it could
      // be a fully-qualified name. If it's an Outer.Inner pair, we identify
      // that via the heuristic that there are only two elements if we split on
      // the dot and that the whole string is capital
      if (typeRawName.indexOf('.') == typeRawName.lastIndexOf('.') && isCapital(typeRawName)) {
        className = typeRawName;
        packageName = getPackageFromClassName(typeRawName.substring(0, typeRawName.indexOf('.')));
      } else {
        packageName = typeRawName.substring(0, typeRawName.lastIndexOf("."));
        className = typeRawName.substring(typeRawName.lastIndexOf(".") + 1);
      }
    } else {
      className = typeRawName;
      packageName = getPackageFromClassName(className);
    }

    if (isTypeVar(className)) {
      // don't create synthetic classes for in-scope type variables
      return;
    }

    classToUpdate =
        new UnsolvedClassOrInterface(
            className, packageName, isInsideCatchBlockParameter, isAnInterface);

    classToUpdate.setNumberOfTypeVariables(numberOfArguments);
    classToUpdate.setPreferedTypeVariables(preferredTypeVariables);

    updateMissingClass(classToUpdate);
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
    return existingClassesToFilePath.containsKey(nodeScope.calculateResolvedType().describe());
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
    return variableDeclaration + " = " + getInitializerRHS(variableType);
  }

  /**
   * Returns a type-compatible initializer for a field of the given type.
   *
   * @param variableType the type of the field
   * @return a type-compatible initializer
   */
  private static String getInitializerRHS(String variableType) {
    switch (variableType) {
      case "byte":
        return "(byte)0";
      case "short":
        return "(short)0";
      case "int":
        return "0";
      case "long":
        return "0L";
      case "float":
        return "0.0f";
      case "double":
        return "0.0d";
      case "char":
        return "'\\u0000'";
      case "boolean":
        return "false";
      default:
        return "null";
    }
  }

  /**
   * Updates the list of target files if the given type extends another class or interface and its
   * class file is present in the original codebase.
   *
   * <p>Note: this method only updates the list of target files if the inheritance is resolved.
   *
   * @param classOrInterfaceType A type that may have inheritance.
   * @return True if the updating process was successful; otherwise, false.
   */
  private boolean updateTargetFilesListForExistingClassWithInheritance(
      ClassOrInterfaceType classOrInterfaceType) {
    String classSimpleName = classOrInterfaceType.getNameAsString();
    String fullyQualifiedName = getPackageFromClassName(classSimpleName) + "." + classSimpleName;

    if (!classfileIsInOriginalCodebase(fullyQualifiedName)) {
      return false;
    }

    ResolvedReferenceType resolvedClass;
    try {
      // since resolvedClass is a ClassOrInterfaceType instance, it is safe to cast it to a
      // ReferenceType.
      resolvedClass =
          JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(classOrInterfaceType);
      if (!resolvedClass.getAllAncestors().isEmpty()) {
        String pathOfThisCurrentType = qualifiedNameToFilePath(fullyQualifiedName);
        if (!addedTargetFiles.contains(pathOfThisCurrentType)) {
          addedTargetFiles.add(pathOfThisCurrentType);
          gotException();
        }
        return true;
      }
      return false;
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      return false;
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
   * Given a node, this method checks if that node is inside an object creation expression (meaning
   * that it belongs to an anonymous class).
   *
   * @param node a node
   * @return true if node is inside an object creation expression
   */
  private boolean insideAnObjectCreation(Node node) {
    while (node.getParentNode().isPresent()) {
      Node parent = node.getParentNode().get();
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
      node = parent;
    }
    throw new RuntimeException("Got a node with no containing class!");
  }

  /**
   * Given a type variable, update the list of synthetic classes accordingly. Node: while the type
   * of the input for this method is ClassOrInterfaceType, it is actually a type variable. Make sure
   * to check with {@link UnsolvedSymbolVisitor#isTypeVar(String)} before calling this method.
   *
   * @param type a type variable to be used as input.
   */
  private void updateSyntheticClassesForTypeVar(ClassOrInterfaceType type) {
    String typeSimpleName = type.getNameAsString();
    for (Map<String, NodeList<ClassOrInterfaceType>> typeScope : typeVariables) {
      if (typeScope.containsKey(typeSimpleName)) {
        NodeList<ClassOrInterfaceType> boundOfType = typeScope.get(typeSimpleName);
        for (int index = 0; index < boundOfType.size(); index++) {
          try {
            boundOfType.get(index).resolve();
          } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
            if (e instanceof UnsolvedSymbolException) {
              this.gotException();
              // quoted from the documentation of Oracle: "A type variable with multiple bounds is a
              // subtype of all the types listed in the bound. If one of the bounds is a class, it
              // must be specified first."
              // If the first bound is also unsolved, it is better to assume it to be a class.
              boolean shouldBeAnInterface = !(index == 0);
              solveSymbolsForClassOrInterfaceType(boundOfType.get(index), shouldBeAnInterface);
            }
          }
        }
      }
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
   * @param className the name of the synthetic class, which may be either simple or fully-qualified
   * @param desiredReturnType the desired return type for this method
   * @param updatingInterface true if this method is being used to update an interface, false for
   *     updating classes
   */
  public void updateUnsolvedClassOrInterfaceWithMethod(
      Node method, String className, String desiredReturnType, boolean updatingInterface) {
    String methodName = "";
    List<String> listOfParameters = new ArrayList<>();
    String accessModifer = "public";
    if (method instanceof MethodCallExpr) {
      methodName = ((MethodCallExpr) method).getNameAsString();
      String packageName = splitName(className).a;
      listOfParameters = getArgumentTypesFromMethodCall(((MethodCallExpr) method), packageName);
    }
    // method is a MethodDeclaration
    else {
      methodName = ((MethodDeclaration) method).getNameAsString();
      accessModifer = ((MethodDeclaration) method).getAccessSpecifier().asString();
      for (Parameter para : ((MethodDeclaration) method).getParameters()) {
        Type paraType = para.getType();
        String paraTypeAsString = paraType.asString();
        try {
          // if possible, opt for fully-qualified names.
          paraTypeAsString = paraType.resolve().describe();
        } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
          // avoiding ignored catch blocks errors.
          listOfParameters.add(paraTypeAsString);
          continue;
        }
        listOfParameters.add(paraTypeAsString);
      }
    }
    String returnType = "";
    if (desiredReturnType.equals("")) {
      returnType = returnNameForMethod(methodName);
    } else {
      returnType = desiredReturnType;
    }
    UnsolvedMethod thisMethod =
        new UnsolvedMethod(
            methodName, returnType, listOfParameters, updatingInterface, accessModifer);
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

    addTypeVariableScope(node.getTypeParameters());

    // since this is a return type of a method, it is a dot-separated identifier
    @SuppressWarnings("signature")
    @DotSeparatedIdentifiers String nodeTypeAsString = nodeType.asString();
    @ClassGetSimpleName String nodeTypeSimpleForm = toSimpleName(nodeTypeAsString);

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

    // These are two places where a checked exception can appear, in a catch phrase or in the
    // declaration of a method. This part handles the second case.
    for (ReferenceType throwType : node.getThrownExceptions()) {
      try {
        throwType.resolve();
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        String typeName = throwType.asString();
        UnsolvedClassOrInterface typeOfThrow =
            new UnsolvedClassOrInterface(typeName, getPackageFromClassName(typeName));
        typeOfThrow.extend("java.lang.Throwable");
        updateMissingClass(typeOfThrow);
      }
    }

    // if the second condition is false, then this method belongs to an anonymous class, which
    // should be handled by the codes above.
    if (node.isAnnotationPresent("Override") && classAndItsParent.containsKey(className)) {
      String parentClassName = classAndItsParent.get(className);
      // A modular program analysis can reason about @Override, hence we need to create a synthetic
      // version for the overriden method if missing.

      // TODO: Tracing the complete inheritance tree to locate the missing class is more ideal.
      // However, due to the limitations of JavaParser, we're unable to inspect each ancestor
      // independently. Instead, we can only obtain the resolved versions of all ancestors of a
      // resolved type at once. If any ancestor remains unresolved, we end up with a not very useful
      // exception.
      if (!classfileIsInOriginalCodebase(parentClassName)) {
        if (nodeType.isReferenceType()) {
          updateUnsolvedClassOrInterfaceWithMethod(
              node,
              parentClassName,
              getPackageFromClassName(nodeTypeSimpleForm) + "." + nodeTypeSimpleForm,
              false);
        } else {
          updateUnsolvedClassOrInterfaceWithMethod(
              node, parentClassName, nodeTypeSimpleForm, false);
        }
      }
    }

    // Process any annotations that may be present in generic parameter types,
    // like Collection<@KeyForBottom ? extends T> (check AnnoInGenericTargetTest)
    for (Parameter param : node.getParameters()) {
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

    processAnnotations(node.getAnnotations());

    Set<String> currentLocalVariables = getParameterFromAMethodDeclaration(node);
    localVariables.addFirst(currentLocalVariables);
    Visitable result = super.visit(node, null);
    localVariables.removeFirst();
    typeVariables.removeFirst();
    return result;
  }

  /**
   * Processes annotations by generating synthetic classes for unresolved annotations
   *
   * @param annotations The annotations to resolve
   */
  public void processAnnotations(NodeList<AnnotationExpr> annotations) {
    for (AnnotationExpr anno : annotations) {
      // If we can resolve the annotation, we do not need to generate a synthetic version
      try {
        anno.resolve();
      } catch (UnsolvedSymbolException ex) {
        UnsolvedClassOrInterface unsolvedAnnotation =
            updateUnsolvedClassWithClassName(anno.getNameAsString(), false, false);

        unsolvedAnnotation.setIsAnAnnotationToTrue();

        // Add annotation parameters, but resolve the annotation parameters to Object;
        // it doesn't matter what type they are synthetically generated as
        if (anno.isNormalAnnotationExpr()) {
          for (MemberValuePair pair : anno.toNormalAnnotationExpr().get().getPairs()) {
            unsolvedAnnotation.addMethod(
                new UnsolvedMethod(
                    pair.getNameAsString(), "Object", Collections.emptyList(), true));
          }
        } else if (anno.isSingleMemberAnnotationExpr()) {
          unsolvedAnnotation.addMethod(
              new UnsolvedMethod("value", "Object", Collections.emptyList(), true));
        }
      }
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
      try {
        className =
            ((MethodCallExpr) expr).resolve().getPackageName()
                + "."
                + ((MethodCallExpr) expr).resolve().getClassName();
      } catch (UnsupportedOperationException e) {
        // This is a limitation of JavaParser. If a method call has a generic return type, sometimes
        // JavaParser can not resolve it.
        // The consequence is that we can not get the class where a method is declared if that
        // method has a generic return type. Hopefully the later version of JavaParser can address
        // this limitation.
        return false;
      }
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
   * solvable because its data is in the jar files that Specimin takes as input.
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
    List<String> argumentsList = getArgumentTypesFromMethodCall(expr, packageName);
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
   * @param nameOfClass the name of an unsolved class. This could be a simple name, but it may also
   *     contain scoping constructs for outer classes. For example, it could be "Outer.Inner".
   *     Alternatively, it may already be a fully-qualified name.
   * @param unsolvedMethods unsolved methods to add to the class before updating this visitor's set
   *     missing classes (optional, may be omitted)
   * @param isExceptionType if the class is of exceptionType
   * @param isUpdatingInterface indicates whether this method is being used to update an interface
   * @return the newly-created UnsolvedClass method, for further processing. This output may be
   *     ignored.
   */
  public UnsolvedClassOrInterface updateUnsolvedClassWithClassName(
      String nameOfClass,
      boolean isExceptionType,
      boolean isUpdatingInterface,
      UnsolvedMethod... unsolvedMethods) {
    // If the name of the class is not present among import statements, we assume that this unsolved
    // class is in the same directory as the current class.

    Pair<String, String> packageAndClassNames = splitName(nameOfClass);
    UnsolvedClassOrInterface result;
    result =
        new UnsolvedClassOrInterface(
            packageAndClassNames.b, packageAndClassNames.a, isExceptionType, isUpdatingInterface);
    for (UnsolvedMethod unsolvedMethod : unsolvedMethods) {
      result.addMethod(unsolvedMethod);
    }
    updateMissingClass(result);
    return result;
  }

  /**
   * Splits a name into the package and class names, based on the upper/lower case heuristic.
   *
   * @param name a simple name, a fully-qualified name, or an inner class name like Outer.Inner
   * @return a pair whose first element is the package name and whose second element is the class
   *     name
   */
  private Pair<String, String> splitName(String name) {
    String packageName = "", simpleClassName = "";

    // Four cases based on these examples: org.pkg.Simple, org.pkg.Simple.Inner, Simple,
    // Simple.Inner
    // Using a heuristic for checking for an FQN: that package names start with lower-case letters,
    // and class names start with upper-class letters.
    if (Character.isLowerCase(name.charAt(0))) {
      // original name assumed to have been fully-qualified
      Iterable<String> parts = Splitter.on('.').split(name);
      for (String part : parts) {
        if (Character.isLowerCase(part.charAt(0))) {
          if ("".equals(packageName)) {
            packageName = part;
          } else {
            packageName += "." + part;
          }
        } else {
          if ("".equals(simpleClassName)) {
            simpleClassName = part;
          } else {
            simpleClassName += "." + part;
          }
        }
      }
    } else {
      // original name assumed to have been simple (but might have inner classes)
      String scope = name.indexOf('.') == -1 ? name : name.substring(0, name.indexOf('.'));
      // If the class name is not purely simple, use the outermost scope.
      packageName = getPackageFromClassName(scope);
      simpleClassName = name;
    }
    return new Pair(packageName, simpleClassName);
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
    List<String> argumentsList = getArgumentTypesFromObjectCreation(expr, packageName);
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
  public boolean isASuperCall(Expression node) {
    if (node instanceof MethodCallExpr) {
      Optional<Expression> caller = node.asMethodCallExpr().getScope();
      if (caller.isEmpty()) {
        return false;
      }
      return caller.get().isSuperExpr();
    } else if (node instanceof FieldAccessExpr) {
      Expression caller = node.asFieldAccessExpr().getScope();
      String fieldName = ((FieldAccessExpr) node).getNameAsString();
      return caller.isSuperExpr()
          || (caller.isThisExpr() && !fieldNameToClassNameMap.containsKey(fieldName));
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
    // If we're inside an object creation, this is an anonymous class. Locate any super things
    // in the class that's being extended.

    String parentClassName;
    try {
      parentClassName = insideAnObjectCreation(expr) ? className : getParentClass(className);
    } catch (RuntimeException e) {
      throw new RuntimeException("crashed while trying to get the parent for " + expr, e);
    }
    if (expr instanceof MethodCallExpr) {
      updateUnsolvedClassOrInterfaceWithMethod(
          expr.asMethodCallExpr(),
          parentClassName,
          methodAndReturnType.getOrDefault(expr.asMethodCallExpr().getNameAsString(), ""),
          false);
    } else if (expr instanceof FieldAccessExpr) {
      String nameAsString = expr.asFieldAccessExpr().getNameAsString();
      updateUnsolvedSuperClassWithFields(
          nameAsString, parentClassName, getPackageFromClassName(parentClassName));
    } else if (expr instanceof NameExpr) {
      String nameAsString = expr.asNameExpr().getNameAsString();
      updateUnsolvedSuperClassWithFields(
          nameAsString, parentClassName, getPackageFromClassName(parentClassName));
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
      UnsolvedClassOrInterface varType =
          new UnsolvedClassOrInterface(variableType, getPackageFromClassName(variableType));
      syntheticTypes.add(variableType);
      relatedClass.addFields(
          setInitialValueForVariableDeclaration(
              variableType, varType.getQualifiedClassName() + " " + var));
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
    for (Map<String, NodeList<ClassOrInterfaceType>> scope : typeVariables) {
      if (scope.containsKey(typeName)) {
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
    Map<String, NodeList<ClassOrInterfaceType>> typeVariableScope = new HashMap<>();
    for (TypeParameter t : typeParameters) {
      typeVariableScope.put(t.getNameAsString(), t.getTypeBound());
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
   * This method checks if the current run of UnsolvedSymbolVisitor can solve the types of the
   * arguments of a method call or similar structure (e.g., constructor invocation)
   *
   * @param argList the arguments to check
   * @return true if UnsolvedSymbolVisitor can solve the types of parameters of method-like
   */
  public static boolean canSolveArguments(NodeList<Expression> argList) {
    if (argList.isEmpty()) {
      return true;
    }
    for (Expression arg : argList) {
      if (arg.isLambdaExpr() || arg.isMethodReferenceExpr()) {
        // Skip lambdas and method refs here and treat them specially later.
        continue;
      }
      if (!canBeSolved(arg)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Given a method call, this method returns the list of types of the parameters of that method
   *
   * @param method the method to be analyzed
   * @param pkgName the name of the package of the class that contains the method being called. This
   *     is only used when creating a functional interface if one of the parameters is a lambda. If
   *     this argument is null, then this method throws if it encounters a lambda.
   * @return the types of parameters of method
   */
  public List<String> getArgumentTypesFromMethodCall(
      MethodCallExpr method, @Nullable String pkgName) {
    NodeList<Expression> argList = method.getArguments();
    return getArgumentTypesImpl(argList, pkgName);
  }

  /**
   * Given a ClassOrInterfaceType, this method returns the qualifed name of that type.
   *
   * @param type a ClassOrInterfaceType instance.
   * @return the qualifed name of type
   */
  public String getQualifiedNameForClassOrInterfaceType(ClassOrInterfaceType type) {
    String typeAsString = type.toString();
    if (typeAsString.contains("<")) {
      typeAsString = typeAsString.substring(0, typeAsString.indexOf("<"));
    }
    String typeSimpleName = type.getName().asString();
    if (!typeAsString.equals(typeSimpleName)) {
      // check for inner classes.
      List<String> splitType = Splitter.on('.').splitToList(typeAsString);
      if (splitType.size() > 2) {
        // if the above conditions are met, this type is probably already in the qualified form.
        return typeAsString;
      } else if (isCapital(typeAsString)) {
        // Heuristic: if the type name has two dot-separated components and
        // the first one is capitalized, then it's probably an inner class.
        // Return the outer class' package.
        String outerClass = splitType.get(0);
        return getPackageFromClassName(outerClass) + "." + typeAsString;
      }
    }
    return getPackageFromClassName(typeSimpleName) + "." + typeSimpleName;
  }

  /**
   * Given a new object creation, this method returns the list of types of the parameters of that
   * call
   *
   * @param creationExpr the object creation call
   * @param pkgName the name of the package of the class that contains the constructor being called.
   *     This is only used when creating a functional interface if one of the parameters is a
   *     lambda. If this argument is null, then this method throws if it encounters a lambda.
   * @return the types of parameters of the object creation method
   */
  public List<String> getArgumentTypesFromObjectCreation(
      ObjectCreationExpr creationExpr, @Nullable String pkgName) {
    NodeList<Expression> argList = creationExpr.getArguments();
    return getArgumentTypesImpl(argList, pkgName);
  }

  /**
   * Shared implementation for getting argument types from method calls or calls to constructors.
   *
   * @param argList list of arguments
   * @param pkgName the name of the package of the class that contains the method being called. This
   *     is only used when creating a functional interface if one of the parameters is a lambda. If
   *     this argument is null, then this method throws if it encounters a lambda
   * @return the list of argument types
   */
  private List<String> getArgumentTypesImpl(
      NodeList<Expression> argList, @Nullable String pkgName) {
    List<String> parametersList = new ArrayList<>();
    for (Expression arg : argList) {
      // Special case for lambdas: don't try to resolve their type,
      // and instead compute their arity and provide an appropriate
      // functional interface from java.util.function.
      if (arg.isLambdaExpr()) {
        if (pkgName == null) {
          throw new RuntimeException("encountered a lambda when the package name was unknown");
        }
        LambdaExpr lambda = arg.asLambdaExpr();
        parametersList.add(resolveLambdaType(lambda, pkgName));
        continue;
      } else if (arg.isMethodReferenceExpr()) {
        // TODO: is there a better way to handle this? How should we know
        // what the type is? The method ref is sometimes not solvable here.
        // Maybe we will need to handle this in JavaTypeCorrect?
        parametersList.add("java.util.function.Supplier<?>");
        continue;
      }

      ResolvedType type = arg.calculateResolvedType();
      // for reference type, we need the fully-qualified name to avoid having to add additional
      // import statements.
      if (type.isReferenceType()) {
        ResolvedReferenceType rrType = type.asReferenceType();
        // avoid creating methods with raw parameter types
        int ctypevar = rrType.getTypeParametersMap().size();
        String typevars = "";
        if (ctypevar != 0) {
          typevars =
              "<"
                  + String.join(", ", Collections.nCopies(ctypevar, "?").toArray(new String[0]))
                  + ">";
        }
        parametersList.add(rrType.getQualifiedName() + typevars);
      } else if (type.isPrimitive()) {
        parametersList.add(type.describe());
      } else if (type.isArray()) {
        parametersList.add(type.asArrayType().describe());
      } else if (type.isNull()) {
        // No way to know what the type should be, so use top.
        parametersList.add("java.lang.Object");
      } else if (type.isTypeVariable()) {
        parametersList.add(type.asTypeVariable().describe());
      }
      // TODO: should we raise an exception here if there is some other kind of type? Could
      // any other type (e.g., a type variable) possibly flow here? I think it's possible.
    }
    return parametersList;
  }

  /**
   * Resolves a type for a lambda expression, possibly by creating a new functional interface.
   *
   * @param lambda the lambda expression
   * @param pkgName the package in which a new functional interface should be created, if necessary
   * @return the fully-qualified name of a functional interface that is in-scope and is a supertype
   *     of the given lambda, according to javac's arity-based typechecking rules for functions
   */
  private String resolveLambdaType(LambdaExpr lambda, String pkgName) {
    int cparam = lambda.getParameters().size();
    boolean isvoid = isLambdaVoidReturn(lambda);
    // we need to run at least once more to solve the functional interface we're about to create
    this.gotException();
    // check arity:
    if (cparam == 0) {
      return "java.util.function.Supplier<?>";
    } else if (cparam == 1 && isvoid) {
      return "java.util.function.Consumer<?>";
    } else if (cparam == 1 && !isvoid) {
      return "java.util.function.Function<?, ?>";
    } else if (cparam == 2 && !isvoid) {
      return "java.util.function.BiFunction<?, ?, ?>";
    } else {
      String funcInterfaceName =
          isvoid ? "SyntheticConsumer" + cparam : "SyntheticFunction" + cparam;
      UnsolvedClassOrInterface funcInterface =
          new UnsolvedClassOrInterface(funcInterfaceName, pkgName, false, true);
      int ctypeVars = cparam + (isvoid ? 0 : 1);
      funcInterface.setNumberOfTypeVariables(ctypeVars);
      String[] paramArray = funcInterface.getTypeVariablesAsStringWithoutBrackets().split(", ");
      List<String> params = List.of(paramArray);
      if (!isvoid) {
        // remove the last element of params, because that's the return type, not a parameter
        params = params.subList(0, params.size() - 1);
      }
      String returnType = isvoid ? "void" : "T" + cparam;
      UnsolvedMethod apply = new UnsolvedMethod("apply", returnType, params, true);
      funcInterface.addMethod(apply);
      updateMissingClass(funcInterface);

      StringBuilder typeArgs = new StringBuilder();
      typeArgs.append("<");
      for (int i = 0; i < ctypeVars; ++i) {
        typeArgs.append("?");
        if (i != ctypeVars - 1) {
          typeArgs.append(", ");
        }
      }
      typeArgs.append(">");
      return funcInterfaceName + typeArgs;
    }
  }

  /**
   * Determines if a lambda has a void return.
   *
   * @param lambda a lambda expression
   * @return true iff the lambda has a void return
   */
  private boolean isLambdaVoidReturn(LambdaExpr lambda) {
    if (lambda.getExpressionBody().isPresent()) {
      return false;
    }
    BlockStmt body = lambda.getBody().asBlockStmt();
    return body.stream().noneMatch(node -> node instanceof ReturnStmt);
  }

  /**
   * Given a class name, this method returns the corresponding package name.
   *
   * @param className the name of a class, optionally with type arguments.
   * @return the package of that class.
   */
  public String getPackageFromClassName(String className) {
    if (className.contains("<")) {
      className = className.substring(0, className.indexOf("<"));
    }
    if (JavaLangUtils.isJavaLangName(className)) {
      // it's important not to accidentally put java.lang classes
      // (like e.g., Exception or Throwable) into a wildcard import
      // or the current package.
      return "java.lang";
    }
    String pkg = classAndPackageMap.get(className);
    if (pkg != null) {
      return pkg;
    } else {
      // Check if there is a wildcard import. If there isn't always use
      // currentPackage.
      if (wildcardImports.size() == 0) {
        return currentPackage;
      }
      // If there is a wildcard import, check if there is a matching class
      // in the original codebase in the current package. If so, use that.
      if (classfileIsInOriginalCodebase(currentPackage + "." + className)) {
        return currentPackage;
      }
      // If not, then check for each wildcard import if the original codebase
      // contains an appropriate class. If so, use it.
      for (String wildcardPkg : wildcardImports) {
        if (classfileIsInOriginalCodebase(wildcardPkg + "." + className)) {
          return wildcardPkg;
        }
      }
      // If none do, then default to the first wildcard import.
      // TODO: log a warning about this once we have a logger
      String wildcardPkg = wildcardImports.get(0);
      return wildcardPkg;
    }
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

    // The method calculateResolvedType() gets lazy and lacks precision when it comes to handling
    // ObjectCreationExpr instances, thus requiring separate treatment for ObjectCreationExpr.

    // Note: JavaParser's lazy approach to ObjectCreationExpr when it comes to
    // calculateResolvedType() is reasonable, as the return type typically corresponds to the class
    // itself. Consequently, JavaParser does not actively search for constructor declarations within
    // the class. While this approach suffices for compilable input, it is inadequate for handling
    // incomplete synthetic classes, such as in our case.
    if (expr instanceof ObjectCreationExpr) {
      try {
        expr.asObjectCreationExpr().resolve();
        return true;
      } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
        return false;
      }
    }
    try {
      ResolvedType resolvedType = expr.calculateResolvedType();
      if (resolvedType.isTypeVariable()) {
        for (ResolvedTypeParameterDeclaration.Bound bound :
            resolvedType.asTypeParameter().getBounds()) {
          bound.getType().asReferenceType();
        }
      }
      return true;
    } catch (Exception e) {
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
  public @FullyQualifiedName String getIncompleteClass(MethodCallExpr method) {
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
    } else if (callerExpression instanceof ResolvedTypeVariable) {
      String typeSimpleName = callerExpression.asTypeVariable().describe();
      for (Map<String, NodeList<ClassOrInterfaceType>> typeScope : typeVariables) {
        if (typeScope.containsKey(typeSimpleName)) {
          // a type parameter can extend a class and many interfaces. However, the class will always
          // be listed first.
          return JavaParserUtil.classOrInterfaceTypeToResolvedReferenceType(
                  typeScope.get(typeSimpleName).get(0))
              .getQualifiedName();
        }
      }
    }
    throw new RuntimeException("Unexpected expression: " + callerExpression);
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
    if (JavaLangUtils.inJdkPackage(qualifiedName)) {
      return;
    }

    // If the input contains something simple like Map.Entry,
    // try to avoid creating a synthetic class Entry in package Map if there is
    // also a synthetic class for a Map elsewhere (make it an inner class instead).
    // There are two possibilities for how this might be encoded:
    // 1. the "qualified name" might be "Map.Entry", or
    // 2. the class' "simple name" might have a dot in it. For example, the package
    //    name might be "java.util" and the class name might be "Map.Entry".
    String outerClassName = null, innerClassName = null;
    // First case, looking for "Map.Entry" pattern
    if (isCapital(qualifiedName)
        &&
        // This test checks that it has only one .
        qualifiedName.indexOf('.') == qualifiedName.lastIndexOf('.')) {
      outerClassName = qualifiedName.substring(0, qualifiedName.indexOf('.'));
      innerClassName = qualifiedName.substring(qualifiedName.indexOf('.') + 1);
    }
    // Second case, looking for "org.example.Map.Entry"-style
    String simpleName = missedClass.getClassName();
    if (simpleName.indexOf('.') != -1) {
      outerClassName = simpleName.substring(0, simpleName.indexOf('.'));
      innerClassName = simpleName.substring(simpleName.indexOf('.') + 1);
    }

    if (innerClassName != null && outerClassName != null) {
      for (UnsolvedClassOrInterface e : missingClass) {
        if (e.getClassName().equals(outerClassName)) {
          UnsolvedClassOrInterface innerClass =
              new UnsolvedClassOrInterface.UnsolvedInnerClass(innerClassName, e.getPackageName());
          updateMissingClassHelper(missedClass, innerClass);
          e.addInnerClass(innerClass);
          return;
        }
      }
      // The outer class doesn't exist yet. Create it.
      UnsolvedClassOrInterface outerClass =
          new UnsolvedClassOrInterface(
              outerClassName, missedClass.getPackageName(), false, missedClass.isAnInterface());
      UnsolvedClassOrInterface innerClass =
          new UnsolvedClassOrInterface.UnsolvedInnerClass(
              innerClassName, missedClass.getPackageName());
      updateMissingClassHelper(missedClass, innerClass);
      outerClass.addInnerClass(innerClass);
      missingClass.add(outerClass);
      return;
    }

    for (UnsolvedClassOrInterface e : missingClass) {
      if (e.equals(missedClass)) {
        updateMissingClassHelper(missedClass, e);
        return;
      }
    }
    missingClass.add(missedClass);
  }

  /**
   * This helper method updates the missing class to with anything in from. The missing classes must
   * both represent the same class semantically for it to be sensible to call this method.
   *
   * @param from the class or interface to use as a source
   * @param to the class or interface to be updated
   */
  private void updateMissingClassHelper(
      UnsolvedClassOrInterface from, UnsolvedClassOrInterface to) {
    // add new methods
    for (UnsolvedMethod method : from.getMethods()) {
      // No need to check for containment, since the methods are stored
      // as a set (which does not permit duplicates).
      to.addMethod(method);
    }

    // add new fields
    for (String variablesDescription : from.getClassFields()) {
      to.addFields(variablesDescription);
    }
    if (from.getNumberOfTypeVariables() > 0) {
      to.setNumberOfTypeVariables(from.getNumberOfTypeVariables());
    }

    // if a "class" is found to be an interface even once (because it appears
    // in an implements clause), then it must be an interface and not a class.
    if (from.isAnInterface()) {
      to.setIsAnInterfaceToTrue();
    }
  }

  /**
   * Given the qualified name of a class, this method determines if the corresponding class file
   * exists in the original input codebase.
   *
   * @param qualifiedName the qualified name of a class.
   * @return true if the corresponding class file is originally in the input codebase.
   */
  public boolean classfileIsInOriginalCodebase(String qualifiedName) {
    return this.existingClassesToFilePath.containsKey(qualifiedName);
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
              + " getSimpleSyntheticClassFromFullyQualifiedName. Non-classpath-like name: "
              + fullyName);
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
      String callerExpressionString = callerExpression.get().toString();
      return classAndPackageMap.containsKey(callerExpressionString)
          || looksLikeSimpleClassName(callerExpressionString);
    }
  }

  /**
   * Checks if the given string looks like it could be a simple class name. This is a coarse
   * approximation that should be avoided if possible, because it relies on Java convention instead
   * of semantics.
   *
   * @param name the purported name
   * @return true if it looks like a simple class name: it starts with an uppercase letter, has no
   *     dots, and is not all uppercase
   */
  private boolean looksLikeSimpleClassName(String name) {
    // this check is not very comprehensive, since a class can be in lowercase, and a method or
    // field can be in uppercase. But since this is without the jar paths, this is the best we can
    // do.
    return Character.isUpperCase(name.charAt(0))
        && name.indexOf('.') == -1
        && !name.toUpperCase(Locale.getDefault()).equals(name);
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
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      String scopeAsString = field.getScope().toString();
      return classAndPackageMap.containsKey(scopeAsString)
          || looksLikeSimpleClassName(scopeAsString);
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
    String packageOfClass = getPackageFromClassName(classCaller);
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
   * Creates a synthetic class corresponding to a static method call.
   *
   * @param methodCall the method call to be used as input, in string form. This _must_ be a
   *     fully-qualified static method call, or this method will throw.
   * @param methodArgTypes the types of the arguments of the method, as strings
   */
  public void updateClassSetWithQualifiedStaticMethodCall(
      String methodCall, List<String> methodArgTypes) {
    List<String> methodParts = methodParts(methodCall);
    updateClassSetWithQualifiedStaticMethodCallImpl(methodParts, methodArgTypes);
  }

  /**
   * Breaks apart a static, fully-qualified method call into its dot-separated parts. Helper method
   * for {@link #updateClassSetWithQualifiedStaticMethodCallImpl(List, List)}; should not be called
   * directly.
   *
   * @param methodCall a fully-qualified static method call
   * @return the list of the parts of the method call
   */
  private List<String> methodParts(String methodCall) {
    String methodCallWithoutParen = methodCall.substring(0, methodCall.indexOf('('));
    List<String> methodParts = Splitter.onPattern("[.]").splitToList(methodCallWithoutParen);
    int lengthMethodParts = methodParts.size();
    if (lengthMethodParts <= 2) {
      throw new RuntimeException(
          "Need to check the method call with unsolvedAndNotSimple before using"
              + " isAnUnsolvedStaticMethodCalledByAQualifiedClassName");
    }
    return methodParts;
  }

  /**
   * Creates a synthetic class corresponding to a static method call.
   *
   * @param method the method call to be used as input
   */
  public void updateClassSetWithStaticMethodCall(MethodCallExpr method) {
    String methodCall = method.toString();
    if (!isAnUnsolvedStaticMethodCalledByAQualifiedClassName(method)) {
      methodCall = toFullyQualifiedCall(method);
    }
    List<String> methodParts = methodParts(methodCall);
    StringBuilder packageName = new StringBuilder(methodParts.get(0));
    int i = 1;
    while (Character.isLowerCase(methodParts.get(i).charAt(0))) {
      packageName.append(".").append(methodParts.get(i));
      i++;
    }
    List<String> methodArguments = getArgumentTypesFromMethodCall(method, packageName.toString());
    updateClassSetWithQualifiedStaticMethodCallImpl(methodParts, methodArguments);
  }

  /**
   * Helper method for {@link #updateClassSetWithQualifiedStaticMethodCall(String, List)} and {@link
   * #updateClassSetWithStaticMethodCall(MethodCallExpr)}. You should always call one of those
   * instead.
   *
   * @param methodParts the parts of the method call
   * @param methodArgTypes the types of the arguments of the method call
   */
  private void updateClassSetWithQualifiedStaticMethodCallImpl(
      List<String> methodParts, List<String> methodArgTypes) {
    // As this code involves complex string operations, we'll use a method call as an example,
    // following its progression through the code.
    // Suppose this is our method call: com.example.MyClass.process()
    // At this point, our method call become: com.example.MyClass.process
    int lengthMethodParts = methodParts.size();
    StringBuilder returnTypeClassName = new StringBuilder(toCapital(methodParts.get(0)));
    StringBuilder packageName = new StringBuilder(methodParts.get(0));
    // According to the above example, methodName will be process
    String methodName = methodParts.get(lengthMethodParts - 1);
    @SuppressWarnings(
        "signature") // this className is from the second-to-last part of a fully-qualified method
    // call, which is the simple name of a class. In this case, it is MyClass.
    @ClassGetSimpleName String className = methodParts.get(lengthMethodParts - 2);
    // After this loop: returnTypeClassName will be ComExample, and packageName will be com.example
    for (int i = 1; i < lengthMethodParts - 2; i++) {
      returnTypeClassName.append(toCapital(methodParts.get(i)));
      packageName.append(".").append(methodParts.get(i));
    }

    // Before we proceed to making a synthetic class, check if the source class
    // is in the original codebase. If so, just add it as a target file instead of
    // proceeding to try to make a synthetic class.
    String qualifiedName = packageName + "." + className;
    if (classfileIsInOriginalCodebase(qualifiedName)) {
      addedTargetFiles.add(qualifiedNameToFilePath(qualifiedName));
      gotException();
      return;
    }

    // At this point, returnTypeClassName will be ComExampleMyClassProcessReturnType
    returnTypeClassName
        .append(toCapital(className))
        .append(toCapital(methodName))
        .append("ReturnType");
    // since returnTypeClassName is just a single long string without any dot in the middle, it will
    // be a simple name.
    @SuppressWarnings("signature")
    @ClassGetSimpleName String thisReturnType = returnTypeClassName.toString();
    UnsolvedClassOrInterface returnClass =
        new UnsolvedClassOrInterface(thisReturnType, packageName.toString());
    UnsolvedMethod newMethod = new UnsolvedMethod(methodName, thisReturnType, methodArgTypes);
    UnsolvedClassOrInterface classThatContainMethod =
        new UnsolvedClassOrInterface(className, packageName.toString());
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
    // example, following its progression through the code.
    // Suppose this is our field access expression: com.example.MyClass.myField
    List<String> fieldParts = Splitter.onPattern("[.]").splitToList(fieldExpr);
    int numOfFieldParts = fieldParts.size();
    if (numOfFieldParts <= 2) {
      throw new RuntimeException(
          "Need to check this field access expression with"
              + " isAnUnsolvedStaticFieldCalledByAQualifiedClassName before using this method");
    }
    // this is the synthetic type of the field
    StringBuilder fieldTypeClassName = new StringBuilder(toCapital(fieldParts.get(0)));
    StringBuilder packageName = new StringBuilder(fieldParts.get(0));
    // According to the above example, fieldName will be myField
    String fieldName = fieldParts.get(numOfFieldParts - 1);
    @SuppressWarnings(
        "signature") // this className is from the second-to-last part of a fully-qualified field
    // signature, which is the simple name of a class. In this case, it is MyClass.
    @ClassGetSimpleName String className = fieldParts.get(numOfFieldParts - 2);
    // After this loop: fieldTypeClassName will be ComExample, and packageName will be com.example
    for (int i = 1; i < numOfFieldParts - 2; i++) {
      fieldTypeClassName.append(toCapital(fieldParts.get(i)));
      packageName.append(".").append(fieldParts.get(i));
    }
    // At this point, fieldTypeClassName will be ComExampleMyClassMyFieldType
    fieldTypeClassName
        .append(toCapital(className))
        .append(toCapital(fieldName))
        .append("SyntheticType");
    // since fieldTypeClassName is just a single long string without any dot in the middle, it will
    // be a simple name.
    @SuppressWarnings("signature")
    @ClassGetSimpleName String thisFieldType = fieldTypeClassName.toString();
    UnsolvedClassOrInterface typeClass =
        new UnsolvedClassOrInterface(thisFieldType, packageName.toString());
    UnsolvedClassOrInterface classThatContainField =
        new UnsolvedClassOrInterface(className, packageName.toString());
    // at this point, fieldDeclaration will become "ComExampleMyClassMyFieldType myField"
    String fieldDeclaration = fieldTypeClassName + " " + fieldName;
    if (isFinal) {
      fieldDeclaration = "final " + fieldDeclaration;
    }
    if (isStatic) {
      // fieldDeclaration will become "static ComExampleMyClassMyFieldType myField = null;"
      fieldDeclaration = "static " + fieldDeclaration;
    }
    fieldDeclaration =
        setInitialValueForVariableDeclaration(fieldTypeClassName.toString(), fieldDeclaration);
    classThatContainField.addFields(fieldDeclaration);
    classAndPackageMap.put(thisFieldType, packageName.toString());
    classAndPackageMap.put(className, packageName.toString());
    syntheticTypeAndClass.put(thisFieldType, classThatContainField);
    this.updateMissingClass(typeClass);
    this.updateMissingClass(classThatContainField);
  }

  /**
   * Based on the Map returned by JavaTypeCorrect, this method updates the types of methods in
   * synthetic classes.
   *
   * @param typeToCorrect the Map to be analyzed
   * @return true if at least one synthetic type is updated
   */
  public boolean updateTypes(Map<String, String> typeToCorrect) {
    boolean atLeastOneTypeIsUpdated = false;
    for (String incorrectType : typeToCorrect.keySet()) {
      // update incorrectType if it is the type of a field in a synthetic class
      if (syntheticTypeAndClass.containsKey(incorrectType)) {
        UnsolvedClassOrInterface relatedClass = syntheticTypeAndClass.get(incorrectType);
        atLeastOneTypeIsUpdated |=
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
        atLeastOneTypeIsUpdated |=
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
              atLeastOneTypeIsUpdated |=
                  unsolClass.updateFieldByType(incorrectType, typeToCorrect.get(incorrectType));
              this.deleteOldSyntheticClass(unsolClass);
              this.createMissingClass(unsolClass);
            }
          }
        }
      }
    }
    return atLeastOneTypeIsUpdated;
  }

  /**
   * Based on the map returned by JavaTypeCorrect, this method corrects the extends/implements
   * clauses for synthetic classes as needed.
   *
   * @param typesToExtend the set of synthetic types that need to be updated
   * @return true if at least one synthetic type is updated.
   */
  public boolean updateTypesWithExtends(Map<String, String> typesToExtend) {
    boolean atLeastOneTypeIsUpdated = false;
    Set<UnsolvedClassOrInterface> modifiedClasses = new HashSet<>();

    for (String typeToExtend : typesToExtend.keySet()) {
      String extendedType = typesToExtend.get(typeToExtend);

      // Special case for types with the form Class<X>. In this case, the incompatibility
      // is in the type variable X (which is probably a synthetic class whose .class literal
      // is used by the target), not in Class itself.
      if (JavaLangUtils.bothAreJavaLangClass(typeToExtend, extendedType)) {
        // Remove the Class<>
        typeToExtend =
            typeToExtend.substring(typeToExtend.indexOf('<') + 1, typeToExtend.length() - 1);
        extendedType =
            extendedType.substring(extendedType.indexOf('<') + 1, extendedType.length() - 1);
      }
      if (extendedType.startsWith("? extends ")) {
        extendedType = extendedType.substring(10);
      }

      Iterator<UnsolvedClassOrInterface> iterator = missingClass.iterator();
      while (iterator.hasNext()) {
        UnsolvedClassOrInterface missedClass = iterator.next();
        // typeToExtend can be either a simple name or an FQN, due to the limitations
        // of Javac
        String missedClassBefore = missedClass.toString();
        boolean success = missedClass.extend(typeToExtend, extendedType, this);
        if (success) {
          iterator.remove();
          modifiedClasses.add(missedClass);
          this.deleteOldSyntheticClass(missedClass);
          this.createMissingClass(missedClass);
          // Only count an update if the text of the synthetic class changes, to avoid infinite
          // loops.
          atLeastOneTypeIsUpdated |= !missedClassBefore.equals(missedClass.toString());
        }
      }
    }

    missingClass.addAll(modifiedClasses);
    return atLeastOneTypeIsUpdated;
  }

  /**
   * Updates the types for fields or methods in a synthetic class.
   *
   * @param className The name of the synthetic class.
   * @param packageName The package of the synthetic class.
   * @param updateAField True if updating the type of a field, false to update the type of a method.
   * @param incorrectTypeName The name of the current incorrect type.
   * @param correctTypeName The name of the desired correct type.
   * @return true if the update is successful.
   */
  public boolean updateTypeForSyntheticClasses(
      String className,
      String packageName,
      boolean updateAField,
      String incorrectTypeName,
      String correctTypeName) {
    // Make sure that correctTypeName is fully qualified, so that we don't need to
    // add an import to the synthetic class.
    correctTypeName = lookupFQNs(correctTypeName);
    boolean updatedSuccessfully = false;
    UnsolvedClassOrInterface classToSearch = new UnsolvedClassOrInterface(className, packageName);
    Iterator<UnsolvedClassOrInterface> iterator = missingClass.iterator();
    while (iterator.hasNext()) {
      UnsolvedClassOrInterface missedClass = iterator.next();
      // Class comparison is based on class name and package name only.
      if (missedClass.equals(classToSearch)) {
        iterator.remove(); // Remove the outdated version of this synthetic class from the list
        if (updateAField) {
          updatedSuccessfully |= missedClass.updateFieldByType(incorrectTypeName, correctTypeName);
        } else {
          updatedSuccessfully |=
              missedClass.updateMethodByReturnType(incorrectTypeName, correctTypeName);
        }
        missingClass.add(missedClass); // Add the modified missedClass back to the list
        this.deleteOldSyntheticClass(missedClass);
        this.createMissingClass(missedClass);
        // incorrectTypeName has to be synthetic, so it will be in the same package as the use
        String fullyQualifiedIncorrectTypeName =
            missedClass.getPackageName() + "." + incorrectTypeName;
        this.migrateType(fullyQualifiedIncorrectTypeName, correctTypeName);
        return updatedSuccessfully;
      }
    }
    throw new RuntimeException("Could not find the corresponding missing class!");
  }

  /**
   * Lookup the fully-qualified names of each type in the given string, and replace the simple type
   * names in the given string with their fully-qualified equivalents. Return the result.
   *
   * @param javacType a type from javac
   * @return that same type, with simple names in the class-to-package map replaced with FQNs
   */
  private String lookupFQNs(String javacType) {
    // It's possible that the type could start with a new (synthetic) type variable's declaration.
    // That won't be parseable as a type, so strip it first and then re-add it; it isn't parseable
    // as a type because, technically, it isn't. However, we post-process what we get from javac
    // to add synthetic type variable declarations to some return types (where they'll be placed
    // in front of the method). So, for example, we might have something like <SyntheticTypeVar>
    // SyntheticTypeVar as the input to this method; the first part is the declaration of the type
    // variable, and the second part is a use of the type variable. (There's a test that shows
    // this - LambdaBodyStaticUnsolved2Test.)
    String typeVarDecl, rest;
    if (javacType.startsWith("<")) {
      // + 1 to the index to also include the " " that will trail it
      typeVarDecl = javacType.substring(0, javacType.indexOf('>') + 1);
      rest = javacType.substring(javacType.indexOf('>') + 2);
    } else {
      typeVarDecl = "";
      rest = javacType;
    }
    Visitable parsedJavac = StaticJavaParser.parseType(rest);
    parsedJavac =
        parsedJavac.accept(
            new ModifierVisitor<Void>() {
              @Override
              public Visitable visit(ClassOrInterfaceType type, Void p) {
                if (classAndPackageMap.containsKey(type.asString())) {
                  return new ClassOrInterfaceType(
                      classAndPackageMap.get(type.asString()) + "." + type.asString());
                } else {
                  return super.visit(type, p);
                }
              }
            },
            null);
    return typeVarDecl + parsedJavac.toString();
  }

  /**
   * If and only if synthetic classes exist for both input type names, this method migrates all the
   * content of the sythetic class for the incorrect type name to the synthetic class for the
   * correct type name. This avoid losing information gained about the incorrect type when we
   * correct types, which can otherwise lead to non-compilable outputs.
   *
   * @param incorrectTypeName the fully-qualified incorrect synthetic type
   * @param correctTypeName the fully-qualified correct name of the type
   */
  private void migrateType(String incorrectTypeName, String correctTypeName) {
    // This one may or may not be present. If it is not, exit early and do nothing.
    UnsolvedClassOrInterface correctType = getMissingClassWithQualifiedName(correctTypeName);
    if (correctType == null) {
      return;
    }

    // This one is guaranteed to be present.
    UnsolvedClassOrInterface incorrectType = getMissingClassWithQualifiedName(incorrectTypeName);
    if (incorrectType == null) {
      throw new RuntimeException("could not find a synthetic class matching " + incorrectTypeName);
    }

    updateMissingClassHelper(incorrectType, correctType);
  }

  /**
   * Finds the missing/unsolved class with the given fully-qualified name, if one exists. If there
   * isn't one, returns null.
   *
   * @param fqn a fully-qualified name
   * @return the unsolved class with that name, or null
   */
  private @Nullable UnsolvedClassOrInterface getMissingClassWithQualifiedName(String fqn) {
    for (UnsolvedClassOrInterface candidate : missingClass) {
      if (candidate.getQualifiedClassName().equals(fqn)) {
        return candidate;
      }
    }
    return null;
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
  public void gotException() {
    if (DEBUG) {
      StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
      System.out.println("setting gotException to true from: " + stackTraceElements[2]);
    }
    this.gotException = true;
  }
}
