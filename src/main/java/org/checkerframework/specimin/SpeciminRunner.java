package org.checkerframework.specimin;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.utils.SourceRoot;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;
import org.apache.commons.io.FileUtils;
import org.checkerframework.checker.signature.qual.ClassGetSimpleName;
import org.checkerframework.checker.signature.qual.FullyQualifiedName;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleDecompiler;

/** This class is the main runner for Specimin. Use its main() method to start Specimin. */
public class SpeciminRunner {

  /**
   * The main entry point for Specimin.
   *
   * @param args the arguments to Specimin
   * @throws IOException if there is an exception
   */
  public static void main(String... args) throws IOException {
	  
	 /*
	  * OptionParser class provides methods that will help us to define and parse command-line options.
	  * For example: CLI command>>> tar -czvf archive.tar.gz /home/user
	  * here -czvf are the options that help us understand specific ways we can run this command and/or how the output is supposed to be.
	  * while "archive.tar.gz" and "/home/user" are arguments that we will need to execute this commands using the above options


	  * Please refer to accept command in class definition to understand further.
	  */
    OptionParser optionParser = new OptionParser();
    
    
    /*
     * This option is the root of the source directory of the target files. It is used 
     * for symbol resolution from source code and to organize the output directory.
     * 
     * SPECIMIN will run as follows for a program called my program>>>>> myprogram --root /path/to/source
     * here "root" is the option indicating the following argument "/path/to/source" is the path to root of source code
     */  
    OptionSpec<String> rootOption = optionParser.accepts("root").withRequiredArg();

    var jar = optionParser.accepts("jarPath").withOptionalArg().ofType(String.class);

    // This option is the relative paths to the target file(s) - the .java file(s) containing
    // target method(s) - from the root.
    OptionSpec<String> targetFilesOption = optionParser.accepts("targetFile").withRequiredArg();

    // This option is the target methods, specified in the format
    // class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
    OptionSpec<String> targetMethodsOption = optionParser.accepts("targetMethod").withRequiredArg();

    // This option is the target fields, specified in the format
    // class.fully.qualified.Name#fieldName
    OptionSpec<String> targetFieldsOptions = optionParser.accepts("targetField").withRequiredArg();

    // The directory in which to output the results.
    OptionSpec<String> outputDirectoryOption =
        optionParser.accepts("outputDirectory").withRequiredArg();

    OptionSet options = optionParser.parse(args);

    String jarDirectory = options.valueOf(jar);
    List<String> jarFiles = new ArrayList<>();
    if (jarDirectory != null) {
      jarFiles = getJarFiles(jarDirectory);
    }

    performMinimization(
        options.valueOf(rootOption),
        options.valuesOf(targetFilesOption),
        jarFiles,
        options.valuesOf(targetMethodsOption),
        options.valuesOf(targetFieldsOptions),
        options.valueOf(outputDirectoryOption));
  }

  /**
   * This method acts as an API for users who want to incorporate Specimin as a library into their
   * projects. It offers an easy way to do the minimization job without needing to directly call
   * Specimin's main method.
   *
   * @param root The root directory of the input files.
   * @param targetFiles A list of files that contain the target methods.
   * @param jarPaths Paths to relevant JAR files.
   * @param targetMethodNames A set of target method names to be preserved.
   * @param targetFieldNames A set of target field names to be preserved.
   * @param outputDirectory The directory for the output.
   * @throws IOException if there is an exception
   */
  public static void performMinimization(
      String root,
      List<String> targetFiles,
      List<String> jarPaths,
      List<String> targetMethodNames,
      List<String> targetFieldNames,
      String outputDirectory)
      throws IOException {
    // The set of path of files that have been created by Specimin. We must be careful to delete all
    // those files in the end, because otherwise they can pollute the input directory. To do that,
    // we need to register a shutdown hook with the JVM.
    Set<Path> createdClass = new HashSet<>();
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread() {
              @Override
              public void run() {
                deleteFiles(createdClass);
              }
            });

    performMinimizationImpl(
        root,
        targetFiles,
        jarPaths,
        targetMethodNames,
        targetFieldNames,
        outputDirectory,
        createdClass);
  }

  /**
   * Helper method for performMinimization. The logic of performMinimization is here;
   * performMinimization itself wraps this in a try-finally to ensure that all created files are
   * cleaned up properly in the event of a crash or interrupt.
   *
   * @param root The root directory of the input files.
   * @param targetFiles A list of files that contain the target methods.
   * @param jarPaths Paths to relevant JAR files.
   * @param targetMethodNames A set of target method names to be preserved.
   * @param targetFieldNames A set of target field names to be preserved.
   * @param outputDirectory The directory for the output.
   * @throws IOException if there is an exception
   */
  private static void performMinimizationImpl(
      String root,
      List<String> targetFiles,
      List<String> jarPaths,
      List<String> targetMethodNames,
      List<String> targetFieldNames,
      String outputDirectory,
      Set<Path> createdClass)
      throws IOException {
	  
	  
	  
/*
 * ================================================================================STEP 1: Initialization:============================================================================================
   >>> It ensures that the root directory ends with a trailing slash for string manipulation purposes.
 */
    if (!root.endsWith("/")) {
      root = root + "/";
    }
    
    /*
     * =============================================================================STEP 2: Setting Static Solver:====================================================================================
       >>> This method sets up something called a "symbol solver." 
           Think of it like a helper that understands and can find definitions of classes, methods, and variables in your code.
      	   This method sets up a system that helps the parser understand and find definitions in our Java code, 
           including our project's source code and any additional libraries you are using ( JAVA 17 version libraries).       
     */
    updateStaticSolver(root, jarPaths);

 
    /*
     * =============================================================================STEP 3: Parsing Target Files:====================================================================================
       >>> It parses the target Java files specified in the targetFiles list and stores them in a map (parsedTargetFiles). 
       	   This map associates file paths <KEY> with parsed Abstract Syntax Trees (ASTs) of the Java files <VALUE>.
           Abstract syntax trees are data structures widely used in compilers to represent the structure of program code.     
       >>>  WHAT IS A COMPILATION UNIT?
              A CompilationUnit is a data structure used in Java programming to represent the entire content of a Java source file.
              When we use a parser like StaticJavaParser to read a .java file, it creates a CompilationUnit 
              that represents all the content of that file in a structured way. 
              This allows our program to understand and work with the code without just treating it as plain text.
              We can think of it as a digital blueprint of the Java file.
     */
    Map<String, CompilationUnit> parsedTargetFiles = new HashMap<>();
    for (String targetFile : targetFiles) {
      parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
    }

    /*
     * ==============================================================================STEP 4: Decompiling JAR Files (Optional):========================================================================
       >>> If JAR paths are provided (jarPaths list is not empty), it decompiles the JAR files to Java source files in the root directory using the ConsoleDecompiler tool.
     */
    if (!jarPaths.isEmpty()) {
      List<String> argsToDecompile = new ArrayList<>();
      argsToDecompile.add("--silent");// why is this required?
      argsToDecompile.addAll(jarPaths);// all libraries
      argsToDecompile.add(root);// main source code with issue
      ConsoleDecompiler.main(argsToDecompile.toArray(new String[0]));
      // delete unneccessary legal files
      FileUtils.deleteDirectory(new File(root + "META-INF"));
    }

    /*
     * ===================================================================================STEP 5: Mapping Classes:====================================================================================
       >>> WHAT IS A PRMARY CLASS?
       		A primary class is a class that has the same name as the Java file where the class is declared.	
       >>> HOW MAPPING WORKS BELOW:		
       1. Maps Initialization: We initialize two maps: 
            a. existingClassesToFilePath to keep track of class names and their file paths.
            b. nonPrimaryClassesToPrimaryClass to map non-primary classes (classes not named after their file) to their primary classes.
       2. SourceRoot Setup: We use SourceRoot to manage and parse all Java files in the given root directory.
       3. Parsing Java Files: We call tryToParse() to parse all Java files in the root directory.
       4. Processing Each Java File:
          4.1 We get the file path of the current Java file.
          4.2 We check if the file has a primary type (main class) and get its fully qualified name if it exists.
          4.3 We loop through all class or interface declarations in the file:
               4.3.1 If the class has a fully qualified name, we store its name and file path in the existingClassesToFilePath map.
               4.3.2 If the class is not the primary class, we map it to its primary class in the nonPrimaryClassesToPrimaryClass map.
          4.4 We also loop through all enum declarations in the file and store their names and file paths in the existingClassesToFilePath map.
     */

    Map<String, Path> existingClassesToFilePath = new HashMap<>();
    Map<String, String> nonPrimaryClassesToPrimaryClass = new HashMap<>();
    
 // Initialize SourceRoot to help with parsing the Java files in the specified root directory
    SourceRoot sourceRoot = new SourceRoot(Path.of(root));
    
 // Try to parse all Java files in the root directory
    sourceRoot.tryToParse();
    
 // Loop through all parsed CompilationUnits (each representing a Java file)
    for (CompilationUnit compilationUnit : sourceRoot.getCompilationUnits()) {
    	// Get the path of the current Java file being processed
      Path pathOfCurrentJavaFile =
          compilationUnit.getStorage().get().getPath().toAbsolutePath().normalize();
      
      String primaryTypeQualifiedName = "";
      
   // Check if the primary type is present in the CompilationUnit
      if (compilationUnit.getPrimaryType().isPresent()) {
    	// Get the fully qualified name of the primary type (main class) if it is present
        // Note:the get() is safe because primary type here is definitely not a local declaration,
        // which does not have a fully-qualified name.
        primaryTypeQualifiedName =
            compilationUnit.getPrimaryType().get().getFullyQualifiedName().get();
      }
      
   // Loop through all class or interface declarations in the current CompilationUnit
      for (ClassOrInterfaceDeclaration declaredClass :
          compilationUnit.findAll(ClassOrInterfaceDeclaration.class)) {
        if (declaredClass.getFullyQualifiedName().isPresent()) {
          String declaredClassQualifiedName =
              declaredClass.getFullyQualifiedName().get().toString();
          existingClassesToFilePath.put(declaredClassQualifiedName, pathOfCurrentJavaFile);
          
          // which means this class is not a primary class, and there is a primary class.
          if (!"".equals(primaryTypeQualifiedName)
              && !declaredClassQualifiedName.equals(primaryTypeQualifiedName)) {
            nonPrimaryClassesToPrimaryClass.put(
                declaredClassQualifiedName, primaryTypeQualifiedName);
          }
        }
      }
      for (EnumDeclaration enumDeclaration : compilationUnit.findAll(EnumDeclaration.class)) {
        existingClassesToFilePath.put(
            enumDeclaration.getFullyQualifiedName().get(), pathOfCurrentJavaFile);
      }
    }

    /*
     * ==============================================================================STEP 6: Symbol Resolution and correcting Java types:========================================================================
       >>> Visitors for Symbol Resolution:It initializes and utilizes various visitor classes (UnsolvedSymbolVisitor, JavaTypeCorrect, etc.)
           to resolve unsolved symbols, correct Java types, handle inheritance, and remove unsolved annotations.
     */
    UnsolvedSymbolVisitor addMissingClass =
        new UnsolvedSymbolVisitor(
            root, existingClassesToFilePath, targetMethodNames, targetFieldNames);
    addMissingClass.setClassesFromJar(jarPaths);

    Map<String, String> typesToChange = new HashMap<>();
    Map<String, String> classAndUnresolvedInterface = new HashMap<>();

    // This is a defense against infinite loop bugs. The idea is this:
    // if we encounter the same set of outputs three times, that's a good indication
    // that we're in an infinite loop. But, we sometimes encounter the same set
    // of outputs *twice* during normal operation (because some symbol needs to be
    // solved). So, we track all previous iterations, and if we ever see the same
    // outputs we set "problematicIteration" to that one. If we see that output again,
    // we break the loop below early.
    Set<UnsolvedSymbolVisitorProgress> previousIterations = new HashSet<>();
    UnsolvedSymbolVisitorProgress problematicIteration = null;

    while (addMissingClass.gettingException()) {
      addMissingClass.setExceptionToFalse();
      for (CompilationUnit cu : parsedTargetFiles.values()) {
        addMissingClass.setImportStatement(cu.getImports());
        // it's important to make sure that getDeclarations and addMissingClass will visit the same
        // file for each execution of the loop
        FieldDeclarationsVisitor getDeclarations = new FieldDeclarationsVisitor();
        cu.accept(getDeclarations, null);
        addMissingClass.setFieldNameToClassNameMap(getDeclarations.getFieldAndItsClass());
        cu.accept(addMissingClass, null);
      }
      addMissingClass.updateSyntheticSourceCode();
      createdClass.addAll(addMissingClass.getCreatedClass());
      // since the root directory is updated, we need to update the SymbolSolver
      updateStaticSolver(root, jarPaths);
      parsedTargetFiles = new HashMap<>();
      for (String targetFile : targetFiles) {
        parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
      }
      for (String targetFile : addMissingClass.getAddedTargetFiles()) {
        try {
          parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
        } catch (ParseProblemException e) {
          // These parsing codes cause crashes in the CI. Those crashes can't be reproduced locally.
          // Not sure if something is wrong with VineFlower or Specimin CI. Hence we keep these
          // lines as tech debt.
          // TODO: Figure out why the CI is crashing.
          continue;
        }
      }
      UnsolvedSymbolVisitorProgress workDoneAfterIteration =
          new UnsolvedSymbolVisitorProgress(
              addMissingClass.getPotentialUsedMembers(),
              addMissingClass.getAddedTargetFiles(),
              addMissingClass.getSyntheticClassesAsAStringSet());

      // Infinite loop protection.
      boolean gettingStuck = previousIterations.contains(workDoneAfterIteration);
      if (gettingStuck) {
        if (problematicIteration == null) {
          problematicIteration = workDoneAfterIteration;
        } else if (workDoneAfterIteration.equals(problematicIteration)) {
          // This is the third time that we've made no changes, so we're probably
          // in an infinite loop.
          break;
        }
      } else { // not getting stuck
        if (problematicIteration != null && !problematicIteration.equals(workDoneAfterIteration)) {
          // unset problematicIteration
          problematicIteration = null;
        }
      }
      previousIterations.add(workDoneAfterIteration);

      if (gettingStuck || !addMissingClass.gettingException()) {
        // Three possible cases here:
        // 1: addMissingClass has finished its iteration.
        // 2: addMissingClass is stuck for some unknown reasons.
        // 3: addMissingClass is stuck due to type mismatches, in which the JavaTypeCorrect call
        // below should solve it. In this case (only), we should trigger another round
        // of iteration of the unsolved symbol visitor, since JavaTypeCorrect may have caused
        // some new symbols to be unsolved.

        // update the synthetic types by using error messages from javac.
        GetTypesFullNameVisitor getTypesFullNameVisitor = new GetTypesFullNameVisitor();
        for (CompilationUnit cu : parsedTargetFiles.values()) {
          cu.accept(getTypesFullNameVisitor, null);
        }
        Map<String, Set<String>> filesAndAssociatedTypes =
            getTypesFullNameVisitor.getFileAndAssociatedTypes();
        // correct the types of all related files before adding them to parsedTargetFiles
        JavaTypeCorrect typeCorrecter =
            new JavaTypeCorrect(root, new HashSet<>(targetFiles), filesAndAssociatedTypes);
        typeCorrecter.correctTypesForAllFiles();
        typesToChange = typeCorrecter.getTypeToChange();
        classAndUnresolvedInterface = typeCorrecter.getClassAndUnresolvedInterface();
        boolean changeAtLeastOneType = addMissingClass.updateTypes(typesToChange);
        boolean extendAtLeastOneType =
            addMissingClass.updateTypesWithExtends(typeCorrecter.getExtendedTypes());
        boolean atLeastOneTypeIsUpdated = changeAtLeastOneType || extendAtLeastOneType;

        // this is case 2. We will stop addMissingClass. In the next phase,
        // TargetMethodFinderVisitor will give us a meaningful exception message regarding which
        // element in the input is not solvable.
        if (!atLeastOneTypeIsUpdated && gettingStuck) {
          break;
        } else if (atLeastOneTypeIsUpdated) {
          // this is case 3: ensure that unsolved symbol solver is called at least once, to force us
          // to reach a correct fixpoint
          addMissingClass.gotException();
          continue;
        }

        // in order for the newly updated files to be considered when solving symbols, we need to
        // update the type solver and the map of parsed target files.
        updateStaticSolver(root, jarPaths);
      }
    }

    UnsolvedAnnotationRemoverVisitor annoRemover = new UnsolvedAnnotationRemoverVisitor(jarPaths);
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(annoRemover, null);
    }

    EnumVisitor enumVisitor = new EnumVisitor(targetMethodNames);
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(enumVisitor, null);
    }
    
    /*
     * ==============================================================================STEP 7: Method Pruning :========================================================================
       >>> It prunes methods and fields that are not used by the target methods or classes, removing unnecessary code.
       >>> HOW BELOW CODE WORKS?
       		1. TargetMethodFinderVisitor: This part finds the methods and fields we're targeting in the parsed Java files.
			2. Unfound Methods: If there are any methods that couldn't be found, it throws an error.
			3. SolveMethodOverridingVisitor: This part resolves issues with method overriding.
			4. Related Classes: It collects and parses related Java files that might affect or be affected by the target methods.
			5. Inheritance Information: This loop ensures we find and preserve inheritance information for all relevant classes.
			6. Annotation Removal: Removes unsolved annotations from the newly added files.
			7. MustImplementMethodsVisitor: Ensures that all required methods are implemented in the classes.
			8. PrunerVisitor: Removes methods that are not needed anymore.
			9. Directory Creation and Output: Ensures directories are created as needed and processes the final target files for output, skipping unnecessary ones.
     */

 // Create a TargetMethodFinderVisitor instance. This will help us to find target methods and fields in the parsed files
    TargetMethodFinderVisitor finder =
        new TargetMethodFinderVisitor(
            targetMethodNames,
            targetFieldNames,
            nonPrimaryClassesToPrimaryClass,
            enumVisitor.getUsedEnum());
    
    
    //-------------------------------------------------------------------------------Look for unfound methods-----------------------------------------------------------------------------------------

    
    // We go through each parsed Java file and let the finder look for target methods and fields
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(finder, null);
    }
 // If there are any unfound methods, throw an exception with details
    Map<String, Set<String>> unfoundMethods = finder.getUnfoundMethods();
    if (!unfoundMethods.isEmpty()) {
      throw new RuntimeException(
          "Specimin could not locate the following target methods in the target files:\n"
              + unfoundMethodsTable(unfoundMethods));
    }
 
    
    
  //-------------------------------------------------------------------------------Fix method overriding-----------------------------------------------------------------------------------------
 
    
    
 // We use a SolveMethodOverridingVisitor to resolve method overriding issues
    SolveMethodOverridingVisitor solveMethodOverridingVisitor =
        new SolveMethodOverridingVisitor(
            finder.getTargetMethods(), finder.getUsedMembers(), finder.getUsedTypeElement());
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(solveMethodOverridingVisitor, null);
    }
 // Create a set to keep track of related classes (classes related to target methods)
 // If the file exists (and is not a JDK class), add it to the related classes
    Set<String> relatedClass = new HashSet<>(parsedTargetFiles.keySet());
    // add all files related to the targeted methods
    for (String classFullName : solveMethodOverridingVisitor.getUsedClass()) {
      String directoryOfFile = classFullName.replace(".", "/") + ".java";
      File thisFile = new File(root + directoryOfFile);
      // classes from JDK are automatically on the classpath, so UnsolvedSymbolVisitor will not
      // create synthetic files for them
      if (thisFile.exists()) {
        relatedClass.add(directoryOfFile);
      }
    }

    
    //-------------------------------------------------------------------------------Parsing additional Java files-----------------------------------------------------------------------------------------

    
    
 // Parse any additional related Java files that have not been parsed yet
    for (String directory : relatedClass) {
      // directories already in parsedTargetFiles are original files in the root directory, we are
      // not supposed to update them.
      if (!parsedTargetFiles.containsKey(directory)) {
        try {
          parsedTargetFiles.put(directory, parseJavaFile(root, directory));
        } catch (ParseProblemException e) {
          // TODO: Figure out why the CI is crashing.
          continue;
        }
      }
    }
    
    
    //-------------------------------------------------------------------------------Handling Class inheritance-----------------------------------------------------------------------------------------

    
    
 // Find and preserve class inheritance information
    Set<String> classToFindInheritance = solveMethodOverridingVisitor.getUsedClass();
    Set<String> totalSetOfAddedInheritedClasses = classToFindInheritance;
    InheritancePreserveVisitor inheritancePreserve;
    while (!classToFindInheritance.isEmpty()) {
      inheritancePreserve = new InheritancePreserveVisitor(classToFindInheritance);
      
   // Go through each parsed Java file and let inheritancePreserve process it
      for (CompilationUnit cu : parsedTargetFiles.values()) {
        cu.accept(inheritancePreserve, null);
      }
      
   // Add new classes found by inheritancePreserve
      for (String targetFile : inheritancePreserve.getAddedClasses()) {
        String directoryOfFile = targetFile.replace(".", "/") + ".java";
        File thisFile = new File(root + directoryOfFile);
        // classes from JDK are automatically on the classpath, so UnsolvedSymbolVisitor will not
        // create synthetic files for them
        if (thisFile.exists()) {
          try {
            parsedTargetFiles.put(directoryOfFile, parseJavaFile(root, directoryOfFile));
          } catch (ParseProblemException e) {
            // TODO: Figure out why the CI is crashing.
            continue;
          }
        }
      }
      classToFindInheritance = inheritancePreserve.getAddedClasses();
      totalSetOfAddedInheritedClasses.addAll(classToFindInheritance);
      inheritancePreserve.emptyAddedClasses();
    }

 // Update the set of used classes with the newly added inherited classes
    Set<String> updatedUsedClass = solveMethodOverridingVisitor.getUsedClass();
    updatedUsedClass.addAll(totalSetOfAddedInheritedClasses);

    
    //-----------------------------------------------------------------Removing Annotations from newly added classes----------------------------------------------------------------------------------

    
    
    // remove the unsolved annotations in the newly added files.
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(annoRemover, null);
    }

    updatedUsedClass.addAll(annoRemover.getSolvedAnnotationFullName());

    
    //-----------------------------------------------------------------Ensuring Required methods are implemented----------------------------------------------------------------------------------

    
    
 // Create a MustImplementMethodsVisitor to ensure required methods are implemented
    MustImplementMethodsVisitor mustImplementMethodsVisitor =
        new MustImplementMethodsVisitor(
            solveMethodOverridingVisitor.getUsedMembers(),
            updatedUsedClass,
            existingClassesToFilePath);
 // Go through each parsed Java file and let mustImplementMethodsVisitor process it
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(mustImplementMethodsVisitor, null);
    }

    
    //-------------------------------------------------------------------------------Removing unused classes-------------------------------------------------------------------------------------

    
    
 // Create a PrunerVisitor to remove unused methods
    PrunerVisitor methodPruner =
        new PrunerVisitor(
            finder.getTargetMethods(),
            targetFieldNames,
            mustImplementMethodsVisitor.getUsedMembers(),
            mustImplementMethodsVisitor.getUsedClass(),
            finder.getResolvedYetStuckMethodCall(),
            classAndUnresolvedInterface);

    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(methodPruner, null);
    }
   
   //------------------------------------------------------------------------------- Directory Creation and Output-------------------------------------------------------------------------------------

    	
    	
    // cache to avoid called Files.createDirectories repeatedly with the same arguments
    Set<Path> createdDirectories = new HashSet<>();

    for (Entry<String, CompilationUnit> target : parsedTargetFiles.entrySet()) {
      // ignore classes from the Java package.
      if (target.getKey().startsWith("java/")) {
        continue;
      }
      // If a compilation output's entire body has been removed and the related class is not used by
      // the target methods, do not output it.
      if (isEmptyCompilationUnit(target.getValue())) {
        // target key will have this form: "path/of/package/ClassName.java"
        String classFullyQualfiedName = getFullyQualifiedClassName(target.getKey());
        @SuppressWarnings("signature") // since it's the last element of a fully qualified path
        @ClassGetSimpleName String simpleName =
            classFullyQualfiedName.substring(classFullyQualfiedName.lastIndexOf(".") + 1);
        // If this condition is true, this class is a synthetic class initially created to be a
        // return type of some synthetic methods, but later javac has found the correct return type
        // for that method.
        if (typesToChange.containsKey(simpleName)) {
          continue;
        }
        if (!finder.getUsedTypeElement().contains(classFullyQualfiedName)) {
          continue;
        }
      }
      
      /*
       * ==============================================================================STEP 8: Output Processing :========================================================================
         >>> It prepares and writes the modified Java files (after minimization) to the specified outputDirectory.
       */

   
      
      Path targetOutputPath = Path.of(outputDirectory, target.getKey());
      // Create any parts of the directory structure that don't already exist.
      Path dirContainingOutputFile = targetOutputPath.getParent();
      // This null test is very defensive and might not be required? I think getParent can
      // only return null if its input was a single element path, which targetOutputPath
      // should not be unless the user made an error.
      if (dirContainingOutputFile != null
          && !createdDirectories.contains(dirContainingOutputFile)) {
        Files.createDirectories(dirContainingOutputFile);
        createdDirectories.add(dirContainingOutputFile);
      }
      // Write the string representation of CompilationUnit to the file
      try {
        PrintWriter writer = new PrintWriter(targetOutputPath.toFile(), StandardCharsets.UTF_8);
        writer.print(getCompilationUnitWithCommentsTrimmed(target.getValue()));
        writer.close();
      } catch (IOException e) {
        System.out.println("failed to write output file " + targetOutputPath);
        System.out.println("with error: " + e);
      }
    }
    createdClass.addAll(getPathsFromJarPaths(root, jarPaths));
  }

  /**
   * Helper method to create a human-readable table of the unfound methods and each method in the
   * same class that was considered.
   *
   * @param unfoundMethods the unfound methods and the methods that were considered
   * @return a human-readable string representation
   */
  private static String unfoundMethodsTable(Map<String, Set<String>> unfoundMethods) {
    StringBuilder sb = new StringBuilder();
    for (String unfoundMethod : unfoundMethods.keySet()) {
      sb.append("* ")
          .append(unfoundMethod)
          .append("\n  Considered these methods from the same class:\n");
      for (String consideredMethod : unfoundMethods.get(unfoundMethod)) {
        sb.append("    * ").append(consideredMethod).append("\n");
      }
    }
    return sb.toString();
  }

  /**
   * Update the static solver for JavaParser.
   *
   * @param root the root directory of the files to parse.
   * @param jarPaths the list of jar files to be used as input.
   * @throws IOException if something went wrong.
   */
  private static void updateStaticSolver(String root, List<String> jarPaths) throws IOException {
    // Set up the parser's symbol solver, so that we can resolve definitions.
    CombinedTypeSolver typeSolver =
        new CombinedTypeSolver(new JdkTypeSolver(), new JavaParserTypeSolver(new File(root)));
    for (String path : jarPaths) {
      typeSolver.add(new JarTypeSolver(path));
    }
    JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
    StaticJavaParser.getParserConfiguration().setSymbolResolver(symbolSolver);
    StaticJavaParser.getParserConfiguration()
        .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17);
  }

  /**
   * Converts a path to a Java file into the fully-qualified name of the public class in that file,
   * relying on the file's relative path being the same as the package name.
   *
   * @param javaFilePath the path to a .java file, in this form: "path/of/package/ClassName.java".
   *     Note that this path must be rooted at the same directory in which javac could be invoked to
   *     compile the file
   * @return the fully-qualified name of the given class
   */
  @SuppressWarnings("signature") // string manipulation
  private static @FullyQualifiedName String getFullyQualifiedClassName(final String javaFilePath) {
    String result = javaFilePath.replace("/", ".");
    if (!result.endsWith(".java")) {
      throw new RuntimeException("A Java file path does not end with .java: " + result);
    }
    return result.substring(0, result.length() - 5);
  }

  /**
   * Checks whether the given compilation unit contains nothing. Should conservatively return false
   * by default if unsure.
   *
   * @param cu any compilation unit
   * @return true iff this compilation unit is totally empty and can therefore be safely removed
   *     entirely
   */
  private static boolean isEmptyCompilationUnit(CompilationUnit cu) {
    for (Node child : cu.getChildNodes()) {
      if (child instanceof PackageDeclaration
          || child instanceof ImportDeclaration
          || child instanceof Comment) {
        // Package declarations, imports, and comments don't count for the purposes of
        // deciding whether to entirely remove a compilation unit.
      } else if (child instanceof ClassOrInterfaceDeclaration) {
        ClassOrInterfaceDeclaration cdecl =
            ((ClassOrInterfaceDeclaration) child).asClassOrInterfaceDeclaration();
        if (!cdecl.getMembers().isEmpty()) {
          return false;
        }
      } else {
        return false;
      }
    }
    return true;
  }

  /**
   * Use JavaParser to parse a single Java files.
   *
   * @param root the absolute path to the root of the source tree
   * @param path the path of the file to be parsed, relative to the root
   * @return the compilation unit representing the code in the file at the path, or exit with an
   *     error
   */
  private static CompilationUnit parseJavaFile(String root, String path) throws IOException {
    return StaticJavaParser.parse(Path.of(root, path));
  }

  /**
   * Retrieves the paths of Java files that should be created from the list of JAR files.
   *
   * @param outPutDirectory The directory where the Java files will be created.
   * @param jarPaths The set of paths to JAR files.
   * @return A set containing the paths of the Java files to be created.
   * @throws IOException If an I/O error occurs.
   */
  private static Set<Path> getPathsFromJarPaths(String outPutDirectory, List<String> jarPaths)
      throws IOException {
    Set<Path> pathsOfFile = new HashSet<>();
    for (String path : jarPaths) {
      JarTypeSolver jarSolver = new JarTypeSolver(path);
      for (String qualifedClassName : jarSolver.getKnownClasses()) {
        String relativePath = qualifedClassName.replace(".", "/") + ".java";
        String absolutePath = outPutDirectory + relativePath;
        Path filePath = Paths.get(absolutePath);
        if (Files.exists(filePath)) {
          pathsOfFile.add(filePath);
        }
      }
    }
    return pathsOfFile;
  }

  /**
   * This method delete all files from a set of Paths. If a file is the only file in its parent
   * directory, this method will recursively delete the parent directories until it meets a
   * non-empty directory.
   *
   * @param fileList the set of Paths of files to be deleted
   */
  private static void deleteFiles(Set<Path> fileList) {
    for (Path filePath : fileList) {
      try {
        Files.delete(filePath);
        File classFile = new File(filePath.toString().replace(".java", ".class"));
        // since javac might leave some .class files
        if (classFile.exists()) {
          Files.delete(classFile.toPath());
        }
        File parentDir = filePath.toFile().getParentFile();
        if (parentDir != null && parentDir.exists() && parentDir.isDirectory()) {
          String[] fileContained = parentDir.list();
          if (fileContained != null && fileContained.length == 0) {
            // Recursive call to delete the parent directory
            deleteFileFamily(parentDir);
          }
        }
      } catch (Exception e) {
        throw new RuntimeException("Unresolved file path: " + filePath);
      }
    }
  }

  /**
   * Returns a comment-free version of a compilation unit.
   *
   * @param cu A compilation unit possibly containing comments.
   * @return A comment-free version of the compilation unit.
   */
  private static CompilationUnit getCompilationUnitWithCommentsTrimmed(CompilationUnit cu) {
    CompilationUnit cuWithNoComments = cu;
    for (Comment child : cuWithNoComments.getAllComments()) {
      child.remove();
    }
    return cuWithNoComments;
  }

  /**
   * Given a directory, this method will delete that directory and recursively delete the parent
   * directories until it meets a non-empty directory. Be careful when making any changes to this
   * method, as an incorrect conditional statement could result in the deletion of non-empty
   * directories. This method is used to delete the temporary directory created by
   * UnsolvedSymbolVisitor.
   *
   * @param fileDir the directory of the file to be deleted
   */
  private static void deleteFileFamily(File fileDir) {
    fileDir.delete();
    File parentDir = fileDir.getParentFile();
    if (parentDir != null && parentDir.exists() && parentDir.isDirectory()) {
      String[] fileContained = parentDir.list();
      // Be cautious when making any changes to this line, you might actually delete important
      // directories in the project.
      if (fileContained != null && fileContained.length == 0) {
        deleteFileFamily(parentDir);
      }
    }
  }

  /**
   * Given a directory, this method will return all the .jar files stored in the directory.
   *
   * @param directoryPath the directory of the jar files
   */
  private static List<String> getJarFiles(String directoryPath) throws IOException {
    Path jarPath = Path.of(directoryPath);
    try (Stream<Path> stream = Files.walk(jarPath)) {
      return stream
          .filter(path -> Files.isRegularFile(path) && path.toString().endsWith(".jar"))
          .map(path -> path.toString())
          .collect(Collectors.toList());
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }
}
