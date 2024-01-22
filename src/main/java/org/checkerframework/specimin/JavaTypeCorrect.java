package org.checkerframework.specimin;

import com.google.common.base.Splitter;
import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * This class uses javac to analyze files. If there are any incompatible type errors in those files,
 * this class can suggest changes to be made to the existing types in the input files to solve all
 * the type errors. Note: This class can only solve type errors where there are mismatch between
 * types. For cases where there is type inference failed or unfound symbol, try to use
 * UnsolvedSymbolVisitor to add the missing files to the input first. {@link UnsolvedSymbolVisitor}
 */
class JavaTypeCorrect {

  /** List of the files to correct the types */
  public Set<String> fileNameList;

  /**
   * The root directory of the files in the fileNameList. If there are more than one root
   * directories involved, consider using more than one instances of JavaTypeCorrect
   */
  public String sourcePath;

  /**
   * This map is for type correcting. The key is the name of the current incorrect type, and the
   * value is the name of the desired correct type.
   */
  private Map<String, String> typeToChange;

  /**
   * A map that associates the file directory with the set of fully qualified names of types used
   * within that file.
   */
  private Map<String, Set<String>> fileAndAssociatedTypes = new HashMap<>();

  /**
   * Create a new JavaTypeCorrect instance. The directories of files in fileNameList are relative to
   * rootDirectory, and rootDirectory is an absolute path
   *
   * @param rootDirectory the root directory of the files to correct types
   * @param fileNameList the list of the relative directory of the files to correct types
   */
  public JavaTypeCorrect(
      String rootDirectory,
      Set<String> fileNameList,
      Map<String, Set<String>> fileAndAssociatedTypes) {
    this.fileNameList = fileNameList;
    this.sourcePath = new File(rootDirectory).getAbsolutePath();
    this.typeToChange = new HashMap<>();
    this.fileAndAssociatedTypes = fileAndAssociatedTypes;
  }

  /**
   * Get the value of typeToChange
   *
   * @return the value of typeToChange
   */
  public Map<String, String> getTypeToChange() {
    return typeToChange;
  }

  /**
   * This method updates typeToChange by using javac to run all the files in fileNameList and
   * analyzing the error messages returned by javac
   */
  public void correctTypesForAllFiles() {
    for (String fileName : fileNameList) {
      runJavacAndUpdateTypes(fileName);
    }
  }

  /**
   * This method uses javac to run a file and updates typeToChange if that file has any incompatible
   * type error
   *
   * @param filePath the directory of the file to be analyzed
   */
  public void runJavacAndUpdateTypes(String filePath) {
    try {
      String command = "javac";
      String[] arguments = {command, "-sourcepath", sourcePath, sourcePath + "/" + filePath};
      ProcessBuilder processBuilder = new ProcessBuilder(arguments);
      processBuilder.redirectErrorStream(true);
      Process process = processBuilder.start();
      BufferedReader reader =
          new BufferedReader(
              new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8));
      String line;
      // incorrect constraint type will be updated here. Other types will be updated by
      // updateTypeToChange
      String incorrectConstraintType = "";
      String correctConstraintType = "";
      while ((line = reader.readLine()) != null) {
        if (line.contains("error: incompatible types")) {
          updateTypeToChange(line, filePath);
        }
        // the type error with constraint types will be in a pair of lines:
        // equality constraint: correctType
        // lower bounds: incorrectType
        if (line.contains("equality constraints: ")) {
          correctConstraintType = line.trim().replace("equality constraints: ", "");
        }
        if (line.contains("lower bounds: ")) {
          incorrectConstraintType = line.trim().replace("lower bounds: ", "");
          typeToChange.put(incorrectConstraintType, correctConstraintType);
        }
      }
    } catch (Exception e) {
      // TODO: We either want to leave a comment as to why we are ignoring
      // TODO: or we need to throw an exception, such as a new RuntimeException
      // Do we want to just print the exception? This seems incorrect.
      System.out.println(e);
    }
  }

  /**
   * This method updates typeToChange by relying on the error messages from javac
   *
   * @param errorMessage the error message to be analyzed
   * @param filePath the path of the file where this error happens
   */
  private void updateTypeToChange(String errorMessage, String filePath) {
    List<String> splitErrorMessage = Splitter.onPattern("\\s+").splitToList(errorMessage);
    if (splitErrorMessage.size() < 7) {
      throw new RuntimeException("Unexpected type error messages: " + errorMessage);
    }
    /* There are two possible forms of error messages here:
     * 1. error: incompatible types: <type1> cannot be converted to <type2>
     * 2. error: incompatible types: found <type1> required <type2>
     */
    if (errorMessage.contains("cannot be converted to")) {
      String incorrectType = splitErrorMessage.get(4);
      String correctType = splitErrorMessage.get(splitErrorMessage.size() - 1);
      typeToChange.put(incorrectType, tryResolveFullyQualifiedType(correctType, filePath));
    } else {
      String incorrectType = splitErrorMessage.get(5);
      String correctType = splitErrorMessage.get(splitErrorMessage.size() - 1);
      typeToChange.put(incorrectType, tryResolveFullyQualifiedType(correctType, filePath));
    }
  }

  /**
   * This method tries to get the fully-qualified name of a type based on the simple name of that
   * type and the class file where that type is used.
   *
   * @param type the type to be taken as input
   * @param filePath the path of the file where type is used
   * @return the fully-qualified name of that type if any. Otherwise, return the original expression
   *     of type.
   */
  public String tryResolveFullyQualifiedType(String type, String filePath) {
    // type is already in the fully qualifed format
    if (Splitter.onPattern("\\.").splitToList(type).size() > 1) {
      return type;
    }
    if (fileAndAssociatedTypes.containsKey(filePath)) {
      Set<String> fullyQualifiedType = fileAndAssociatedTypes.get(filePath);
      for (String typeFullName : fullyQualifiedType) {
        if (typeFullName.substring(typeFullName.lastIndexOf(".") + 1).equals(type)) {
          return typeFullName;
        }
      }
    }
    return type;
  }
}
