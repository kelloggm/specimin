package org.checkerframework.specimin;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** A visitor that removes unsolved annotation expressions. */
public class UnsolvedAnnotationRemoverVisitor extends ModifierVisitor<Void> {
  /**
   * List of paths of jar files to be used as input. Note: this is the set of every jar path, not
   * just the jar paths used by the current compilation unit.
   */
  List<String> jarPaths;

  /** Map every class in the set of jar files to the corresponding jar file */
  Map<String, String> classToJarPath = new HashMap<>();

  /**
   * Map a class to its fully qualified name based on the import statements of the current
   * compilation unit.
   */
  Map<String, String> classToFullClassName = new HashMap<>();

  /** The set of full names of solvable annotations. */
  private Set<String> solvedAnnotationFullName = new HashSet<>();

  /**
   * Create a new instance of UnsolvedAnnotationRemoverVisitor
   *
   * @param jarPaths a list of paths of jar files to be used as input
   */
  public UnsolvedAnnotationRemoverVisitor(List<String> jarPaths) {
    this.jarPaths = jarPaths;
    for (String jarPath : jarPaths) {
      try {
        JarTypeSolver jarSolver = new JarTypeSolver(jarPath);
        for (String fullClassName : jarSolver.getKnownClasses()) {
          classToJarPath.put(fullClassName, jarPath);
        }
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
  }

  /**
   * Get a copy of the set of solved annotations.
   *
   * @return copy a copy of the set of solved annotations.
   */
  public Set<String> getSolvedAnnotationFullName() {
    Set<String> copy = new HashSet<>();
    copy.addAll(solvedAnnotationFullName);
    return copy;
  }

  @Override
  public Node visit(ImportDeclaration decl, Void p) {
    String classFullName = decl.getNameAsString();
    String className = classFullName.substring(classFullName.lastIndexOf(".") + 1);
    classToFullClassName.put(className, classFullName);
    return decl;
  }

  @Override
  public Visitable visit(MarkerAnnotationExpr expr, Void p) {
    processAnnotations(expr);
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(NormalAnnotationExpr expr, Void p) {
    processAnnotations(expr);
    return super.visit(expr, p);
  }

  @Override
  public Visitable visit(SingleMemberAnnotationExpr expr, Void p) {
    processAnnotations(expr);
    return super.visit(expr, p);
  }

  /**
   * Processes annotations by removing annotations that are not solvable by the input list of jar
   * files.
   *
   * @param annotation the annotation to be processed
   */
  public void processAnnotations(AnnotationExpr annotation) {
    String annotationName = annotation.getNameAsString();

    // Never preserve @Override, since it causes compile errors but does not fix them.
    if ("Override".equals(annotationName)) {
      annotation.remove();
      return;
    }

    // If the annotation can be resolved, find its qualified name to prevent removal
    boolean isResolved = true;
    try {
      annotationName = annotation.resolve().getQualifiedName();
    } catch (UnsolvedSymbolException ex) {
      isResolved = false;
    }

    if (!UnsolvedSymbolVisitor.isAClassPath(annotationName)) {
      if (!classToFullClassName.containsKey(annotationName)) {
        // An annotation not imported and from the java.lang package is not our concern.
        if (!JavaLangUtils.isJavaLangName(annotationName)) {
          annotation.remove();
        }
        return;
      }
      annotationName = classToFullClassName.get(annotationName);
    }

    if (!isResolved && !classToJarPath.containsKey(annotationName)) {
      annotation.remove();
    } else {
      solvedAnnotationFullName.add(annotationName);
    }
  }
}
