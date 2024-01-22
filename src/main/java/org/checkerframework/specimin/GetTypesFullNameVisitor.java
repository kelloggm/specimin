package org.checkerframework.specimin;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * A visitor that traverses a Java file's AST and creates a map, associating the file name with the
 * set of types used inside it.
 */
public class GetTypesFullNameVisitor extends ModifierVisitor<Void> {

  /** The directory path of the Java file. */
  private String fileDirectory = "";

  /**
   * A map that associates the file directory with the set of fully qualified names of types used
   * within that file.
   */
  private Map<String, Set<String>> fileAndAssociatedTypes = new HashMap<>();

  /**
   * Get the map of files' directories and types used within those files.
   *
   * @return the value of fileAndAssociatedTypes
   */
  public Map<String, Set<String>> getFileAndAssociatedTypes() {
    return Collections.unmodifiableMap(fileAndAssociatedTypes);
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
    // Nested type classes don't have a separate class file.
    if (!decl.isNestedType()) {
      // Caution: Calling .get() on an Optional without checking if it's present.
      // This will throw NoSuchElementException if the Optional returned by getFullyQualifiedName()
      // is empty.
      fileDirectory = decl.getFullyQualifiedName().get().replace(".", "/") + ".java";
      fileAndAssociatedTypes.put(fileDirectory, new HashSet<>());
    }
    return super.visit(decl, p);
  }

  @Override
  public Visitable visit(ClassOrInterfaceType type, Void p) {
    String typeFullName;
    try {
      typeFullName = type.resolve().getQualifiedName();
    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
      return super.visit(type, p);
    }
    if (fileAndAssociatedTypes.containsKey(fileDirectory)) {
      fileAndAssociatedTypes.get(fileDirectory).add(typeFullName);
      return super.visit(type, p);
    } else {
      throw new RuntimeException(
          "Unexpected files and types: " + fileDirectory + ", " + typeFullName);
    }
  }
}
