package org.checkerframework.specimin;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.SourceRoot;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;
import org.checkerframework.checker.signature.qual.ClassGetSimpleName;
import org.checkerframework.checker.signature.qual.FullyQualifiedName;

/** This class is the main runner for Specimin. Use its main() method to start Specimin. */
public class SpeciminRunner {

  /**
   * The main entry point for Specimin.
   *
   * @param args the arguments to Specimin
   * @throws IOException if there is an exception
   */
  public static void main(String... args) throws IOException {
    OptionParser optionParser = new OptionParser();

    // This option is the root of the source directory of the target files. It is used
    // for symbol resolution from source code and to organize the output directory.
    OptionSpec<String> rootOption = optionParser.accepts("root").withRequiredArg();

    OptionSpec<String> jarPath = optionParser.accepts("jarPath").withOptionalArg();

    // This option is the relative paths to the target file(s) - the .java file(s) containing
    // target method(s) - from the root.
    OptionSpec<String> targetFilesOption = optionParser.accepts("targetFile").withRequiredArg();

    // This option is the target methods, specified in the format
    // class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
    OptionSpec<String> targetMethodsOption = optionParser.accepts("targetMethod").withRequiredArg();

    // The directory in which to output the results.
    OptionSpec<String> outputDirectoryOption =
        optionParser.accepts("outputDirectory").withRequiredArg();

    OptionSet options = optionParser.parse(args);
    performMinimization(
        options.valueOf(rootOption),
        options.valuesOf(targetFilesOption),
        options.valuesOf(jarPath),
        options.valuesOf(targetMethodsOption),
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
   * @param outputDirectory The directory for the output.
   * @throws IOException if there is an exception
   */
  public static void performMinimization(
      String root,
      List<String> targetFiles,
      List<String> jarPaths,
      List<String> targetMethodNames,
      String outputDirectory)
      throws IOException {

    // To facilitate string manipulation in subsequent methods, ensure that 'root' ends with a
    // trailing slash.
    if (!root.endsWith("/")) {
      root = root + "/";
    }

    // Set up the parser's symbol solver, so that we can resolve definitions.
    CombinedTypeSolver typeSolver =
        new CombinedTypeSolver(
            new ReflectionTypeSolver(), new JavaParserTypeSolver(new File(root)));
    for (String path : jarPaths) {
      typeSolver.add(new JarTypeSolver(path));
    }
    JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
    StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);

    // Keys are paths to files, values are parsed ASTs
    Map<String, CompilationUnit> parsedTargetFiles = new HashMap<>();
    for (String targetFile : targetFiles) {
      parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
    }

    // the set of Java files already exist in the input codebase
    Set<Path> existingFiles = new HashSet<>();
    SourceRoot sourceRoot = new SourceRoot(Path.of(root));
    sourceRoot.tryToParse();
    for (CompilationUnit compilationUnit : sourceRoot.getCompilationUnits()) {
      existingFiles.add(compilationUnit.getStorage().get().getPath().toAbsolutePath().normalize());
    }
    UnsolvedSymbolVisitor addMissingClass = new UnsolvedSymbolVisitor(root, existingFiles);
    addMissingClass.setClassesFromJar(jarPaths);

    // The set of path of files that have been created by addMissingClass. We will delete all those
    // files in the end.
    Set<Path> createdClass = new HashSet<>();
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
      TypeSolver newTypeSolver =
          new CombinedTypeSolver(
              new ReflectionTypeSolver(), new JavaParserTypeSolver(new File(root)));
      JavaSymbolSolver newSymbolSolver = new JavaSymbolSolver(newTypeSolver);
      StaticJavaParser.getConfiguration().setSymbolResolver(newSymbolSolver);
      parsedTargetFiles = new HashMap<>();
      for (String targetFile : targetFiles) {
        parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
      }
      for (String targetFile : addMissingClass.getAddedTargetFiles()) {
        parsedTargetFiles.put(targetFile, parseJavaFile(root, targetFile));
      }
    }

    for (CompilationUnit cu : parsedTargetFiles.values()) {
      UnsolvedAnnotationRemoverVisitor annoRemover = new UnsolvedAnnotationRemoverVisitor(jarPaths);
      cu.accept(annoRemover, null);
      annoRemover.processAnnotations(cu);
    }

    // Use a two-phase approach: the first phase finds the target(s) and records
    // what specifications they use, and the second phase takes that information
    // and removes all non-used code.

    TargetMethodFinderVisitor finder = new TargetMethodFinderVisitor(targetMethodNames);

    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(finder, null);
    }

    List<String> unfoundMethods = finder.getUnfoundMethods();
    if (!unfoundMethods.isEmpty()) {
      throw new RuntimeException(
          "Specimin could not locate the following target methods in the target files: "
              + String.join(", ", unfoundMethods));
    }

    Set<String> relatedClass = new HashSet<>(parsedTargetFiles.keySet());
    // add all files related to the targeted methods
    for (String classFullName : finder.getUsedClass()) {
      String directoryOfFile = classFullName.replace(".", "/") + ".java";
      File thisFile = new File(root + directoryOfFile);
      // classes from JDK are automatically on the classpath, so UnsolvedSymbolVisitor will not
      // create synthetic files for them
      if (thisFile.exists()) {
        relatedClass.add(directoryOfFile);
      }
    }
    GetTypesFullNameVisitor getTypesFullNameVisitor = new GetTypesFullNameVisitor();
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(getTypesFullNameVisitor, null);
    }
    Map<String, Set<String>> filesAndAssociatedTypes =
        getTypesFullNameVisitor.getFileAndAssociatedTypes();
    // correct the types of all related files before adding them to parsedTargetFiles
    JavaTypeCorrect typeCorrecter =
        new JavaTypeCorrect(root, relatedClass, filesAndAssociatedTypes);
    typeCorrecter.correctTypesForAllFiles();
    Map<String, String> typesToChange = typeCorrecter.getTypeToChange();
    addMissingClass.updateTypes(typesToChange);

    for (String directory : relatedClass) {
      // directories already in parsedTargetFiles are original files in the root directory, we are
      // not supposed to update them.
      if (!parsedTargetFiles.containsKey(directory)) {
        parsedTargetFiles.put(directory, parseJavaFile(root, directory));
      }
    }
    InheritancePreserveVisitor inheritancePreserve =
        new InheritancePreserveVisitor(finder.getUsedClass());
    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(inheritancePreserve, null);
    }

    PrunerVisitor methodPruner =
        new PrunerVisitor(
            finder.getTargetMethods(), finder.getUsedMembers(), inheritancePreserve.getUsedClass());

    for (CompilationUnit cu : parsedTargetFiles.values()) {
      cu.accept(methodPruner, null);
    }
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
        if (!finder.getUsedClass().contains(classFullyQualfiedName)) {
          continue;
        }
      }
      Path targetOutputPath = Path.of(outputDirectory, target.getKey());
      // Create any parts of the directory structure that don't already exist.
      Path dirContainingOutputFile = targetOutputPath.getParent();
      // This null test is very defensive and might not be required? I think getParent can
      // only return null if its input was a single element path, which targetOutputPath
      // should not be unless the user made an error.
      if (dirContainingOutputFile != null) {
        Files.createDirectories(dirContainingOutputFile);
      }
      // Write the string representation of CompilationUnit to the file
      try {
        PrintWriter writer =
            new PrintWriter(targetOutputPath.toFile(), StandardCharsets.UTF_8.name());
        writer.print(removeCommentsFromCompilationUnit(target.getValue()));
        writer.close();
      } catch (IOException e) {
        System.out.println("failed to write output file " + targetOutputPath);
        System.out.println("with error: " + e);
      }
    }
    // delete all the temporary files created by UnsolvedSymbolVisitor
    deleteFiles(createdClass);
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
      if (child instanceof PackageDeclaration) {
        // Package declarations don't count for the purposes of
        // deciding whether to entirely remove a compilation unit.
        continue;
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
   * Given a compilation unit, this method returns a no-comment version of that compilation unit.
   *
   * @param cu a compilation unit
   * @return cu without any comments
   */
  private static CompilationUnit removeCommentsFromCompilationUnit(CompilationUnit cu) {
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
}
