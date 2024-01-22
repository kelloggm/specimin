package org.checkerframework.specimin;

import com.google.common.base.Splitter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.signature.qual.ClassGetSimpleName;

/**
 * An UnsolvedClass instance is a representation of a class that can not be solved by SymbolSolver.
 * The reason is that the class file is not in the root directory.
 */
public class UnsolvedClass {
  /**
   * Set of methods belongs to the class. Must be a linked set to ensure deterministic iteration
   * order when writing files synthetic classes.
   */
  private final LinkedHashSet<UnsolvedMethod> methods;

  /** The name of the class */
  private final @ClassGetSimpleName String className;

  /**
   * The fields of this class. Must be a linked set to ensure deterministic iteration order when
   * writing files for synthetic classes.
   */
  private final LinkedHashSet<String> classFields;

  /**
   * The name of the package of the class. We rely on the import statements from the source codes to
   * guess the package name.
   */
  private final String packageName;

  /** This field records the number of type variables for this class */
  private int numberOfTypeVariables = 0;

  /** This field records if the class is a custom exception */
  private boolean isExceptionType = false;

  /**
   * Create an instance of UnsolvedClass
   *
   * @param className the name of the class
   * @param packageName the name of the package
   */
  public UnsolvedClass(@ClassGetSimpleName String className, String packageName) {
    this(className, packageName, false);
  }

  /**
   * Create an instance of UnsolvedClass
   *
   * @param className the name of the class
   * @param packageName the name of the package
   * @param isException does the class represents an exception?
   */
  public UnsolvedClass(
      @ClassGetSimpleName String className, String packageName, boolean isException) {
    this.className = className;
    this.methods = new LinkedHashSet<>();
    this.packageName = packageName;
    this.classFields = new LinkedHashSet<>();
    this.isExceptionType = isException;
  }

  /**
   * Get the list of methods from this synthetic class
   *
   * @return the list of methods
   */
  public Set<UnsolvedMethod> getMethods() {
    return methods;
  }

  /**
   * Get the name of this class.
   *
   * @return the name of the class
   */
  public @ClassGetSimpleName String getClassName() {
    return className;
  }

  /**
   * Get the package where this class belongs to
   *
   * @return the value of packageName
   */
  public String getPackageName() {
    return packageName;
  }

  /**
   * Get the fields of this current class
   *
   * @return classVariables
   */
  public Set<String> getClassFields() {
    return classFields;
  }

  /**
   * Add a method to the class
   *
   * @param method the method to be added
   */
  public void addMethod(UnsolvedMethod method) {
    this.methods.add(method);
  }

  /**
   * Add field declaration to the class. We expect something like "int i" or "String y" instead of
   * just "i" and "y"
   *
   * @param variableExpression the expression of the variables to be added
   */
  public void addFields(String variableExpression) {
    this.classFields.add(variableExpression);
  }

  /**
   * This method sets the number of type variables for the current class
   *
   * @param numberOfTypeVariables number of type variable in this class.
   */
  public void setNumberOfTypeVariables(int numberOfTypeVariables) {
    this.numberOfTypeVariables = numberOfTypeVariables;
  }

  /**
   * This method tells the number of type variables for this class
   *
   * @return the number of type variables
   */
  public int getNumberOfTypeVariables() {
    return this.numberOfTypeVariables;
  }

  /**
   * Update the return type of a method. Note: this method is supposed to be used to update
   * synthetic methods, where the return type of each method is distinct.
   *
   * @param currentReturnType the current return type of this method
   * @param desiredReturnType the new return type
   */
  public void updateMethodByReturnType(String currentReturnType, String desiredReturnType) {
    for (UnsolvedMethod method : methods) {
      if (method.getReturnType().equals(currentReturnType)) {
        method.setReturnType(desiredReturnType);
      }
    }
  }

  /**
   * This method updates the types of fields in this class
   *
   * @param currentType the current type
   * @param correctType the desired type
   */
  public void updateFieldByType(String currentType, String correctType) {
    Iterator<String> iterator = classFields.iterator();
    Set<String> newFields = new HashSet<>();
    while (iterator.hasNext()) {
      String fieldDeclared = iterator.next();
      String staticKeyword = "";
      String finalKeyword = "";
      // since these are fields in synthetic classes created by UnsolvedSymbolVisitor, if this field
      // is both static and final, the static keyword will be placed before the final keyword.
      if (fieldDeclared.startsWith("static")) {
        fieldDeclared = fieldDeclared.replace("static ", "");
        staticKeyword = "static ";
      }
      if (fieldDeclared.startsWith("final")) {
        fieldDeclared = fieldDeclared.replace("final ", "");
        finalKeyword = "final ";
      }
      List<String> elements = Splitter.on(' ').splitToList(fieldDeclared);
      // fieldExpression is guaranteed to have the form "TYPE FIELD_NAME". Since this field
      // expression is from a synthetic class, there is no annotation involved, so TYPE has no
      // space.
      String fieldType = elements.get(0);
      String fieldName = elements.get(1);
      if (fieldType.equals(currentType)) {
        iterator.remove();
        newFields.add(
            UnsolvedSymbolVisitor.setInitialValueForVariableDeclaration(
                correctType, staticKeyword + finalKeyword + correctType + " " + fieldName));
      }
    }

    classFields.addAll(newFields);
  }

  /**
   * Return the content of the class as a compilable Java file.
   *
   * @return the content of the class
   */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("package ").append(packageName).append(";\n");
    sb.append("public class ").append(className).append(getTypeVariablesAsString());
    if (isExceptionType) {
      sb.append(" extends Exception");
    }
    sb.append(" {\n");
    for (String variableDeclarations : classFields) {
      sb.append("    " + "public ")
          .append(variableDeclarations)
          .append(";")
          .append(System.lineSeparator());
    }
    for (UnsolvedMethod method : methods) {
      sb.append(method.toString());
    }
    sb.append("}\n");
    return sb.toString();
  }

  /**
   * Return a synthetic representation for type variables of the current class.
   *
   * @return the synthetic representation for type variables
   */
  public String getTypeVariablesAsString() {
    if (numberOfTypeVariables == 0) {
      return "";
    }
    StringBuilder result = new StringBuilder();
    // if class A has three type variables, the expression will be A<T, T1, T2>
    result.append("<");
    for (int i = 0; i < numberOfTypeVariables; i++) {
      String typeExpression = "T" + ((i > 0) ? i : "");
      result.append(typeExpression).append(", ");
    }
    result.delete(result.length() - 2, result.length());
    result.append(">");
    return result.toString();
  }
}
