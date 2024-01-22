package org.checkerframework.specimin;

import java.util.List;

/**
 * An UnsolvedMethod instance is a representation of a method that can not be solved by
 * SymbolSolver. The reason is that the class file of that method is not in the root directory.
 */
public class UnsolvedMethod {
  /** The name of the method */
  private final String name;

  /**
   * The return type of the method. At the moment, we set the return type the same as the class
   * where the method belongs to.
   */
  private String returnType;

  /**
   * The list of parameters of the method. (Right now we won't touch it until the new variant of
   * SymbolSolver is available)
   */
  private List<String> parameterList;

  /** This field is set to true if this method is a static method */
  private boolean isStatic = false;

  /**
   * Create an instance of UnsolvedMethod
   *
   * @param name the name of the method
   * @param returnType the return type of the method
   * @param parameterList the list of parameters for this method
   */
  public UnsolvedMethod(String name, String returnType, List<String> parameterList) {
    this.name = name;
    this.returnType = returnType;
    this.parameterList = parameterList;
  }

  /**
   * Set the value of returnType. This method is used when javac tells us that UnsolvedSymbolVisitor
   * get the return types wrong.
   *
   * @param returnType the return type to bet set for this method
   */
  public void setReturnType(String returnType) {
    this.returnType = returnType;
  }

  /**
   * Get the return type of this method
   *
   * @return the value of returnType
   */
  public String getReturnType() {
    return returnType;
  }

  /**
   * Get the name of this method
   *
   * @return the name of this method
   */
  public String getName() {
    return name;
  }

  /** Set isStatic to true */
  public void setStatic() {
    isStatic = true;
  }

  /**
   * Return the content of the method. Note that the body of the method is stubbed out.
   *
   * @return the content of the method with the body stubbed out
   */
  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    StringBuilder arguments = new StringBuilder();
    for (int i = 0; i < parameterList.size(); i++) {
      String parameter = parameterList.get(i);
      String parameterName = "parameter" + i;
      arguments.append(parameter).append(" ").append(parameterName);
      if (i < parameterList.size() - 1) {
        arguments.append(", ");
      }
    }

    String returnTypeInString = returnType.isEmpty() ? "" : returnType + " ";
    String staticField = isStatic ? "static " : "";

    result
        .append(System.lineSeparator())
        .append("    public ")
        .append(staticField)
        .append(returnTypeInString)
        .append(name)
        .append("(")
        .append(arguments)
        .append(") {")
        .append(System.lineSeparator())
        .append("        throw new Error();")
        .append(System.lineSeparator())
        .append("    }")
        .append(System.lineSeparator());

    return result.toString();
  }
}
