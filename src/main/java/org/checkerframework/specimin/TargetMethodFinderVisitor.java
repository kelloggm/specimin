package org.checkerframework.specimin;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The main visitor for Specimin's first phase, which locates the target method(s) and compiles
 * information on what specifications they use.
 */
public class TargetMethodFinderVisitor extends ModifierVisitor<Void> {
  /**
   * The names of the target methods. The format is
   * class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
   */
  private Set<String> targetMethodNames;

  /**
   * This boolean tracks whether the element currently being visited is inside a target method. It
   * is set by {@link #visit(MethodDeclaration, Void)}.
   */
  private boolean insideTargetMethod = false;

  /** The fully-qualified name of the class currently being visited. */
  private String classFQName = "";

  /**
   * The methods that were actually used by the targets, and therefore ought to have their
   * specifications (but not bodies) preserved. The Strings in the set are the fully-qualified
   * names, as returned by ResolvedMethodDeclaration#getQualifiedSignature.
   */
  private final Set<String> usedMethods = new HashSet<>();

  /**
   * The resolved target methods. The Strings in the set are the fully-qualified names, as returned
   * by ResolvedMethodDeclaration#getQualifiedSignature.
   */
  private final Set<String> targetMethods = new HashSet<>();

  /**
   * A local copy of the input list of methods. A method is removed from this copy when it is
   * located. If the visitor has been run on all source files and this list isn't empty, that
   * usually indicates an error.
   */
  private final List<String> unfoundMethods;

  /**
   * Create a new target method finding visitor.
   *
   * @param methodNames the names of the target methods, the format
   *     class.fully.qualified.Name#methodName(Param1Type, Param2Type, ...)
   */
  public TargetMethodFinderVisitor(List<String> methodNames) {
    targetMethodNames = new HashSet<>();
    targetMethodNames.addAll(methodNames);
    unfoundMethods = new ArrayList<>(methodNames);
  }

  /**
   * Returns the methods that so far this visitor has not located from its target list. Usually,
   * this should be checked after running the visitor to ensure that it is empty.
   *
   * @return the methods that so far this visitor has not located from its target list
   */
  public List<String> getUnfoundMethods() {
    return unfoundMethods;
  }

  /**
   * Get the methods that this visitor has concluded that the target method(s) use, and therefore
   * ought to be retained. The Strings in the set are the fully-qualified names, as returned by
   * ResolvedMethodDeclaration#getQualifiedSignature.
   *
   * @return the used methods
   */
  public Set<String> getUsedMethods() {
    return usedMethods;
  }

  /**
   * Get the target methods that this visitor has encountered so far. The Strings in the set are the
   * fully-qualified names, as returned by ResolvedMethodDeclaration#getQualifiedSignature.
   *
   * @return the target methods
   */
  public Set<String> getTargetMethods() {
    return targetMethods;
  }

  @Override
  public Visitable visit(ClassOrInterfaceDeclaration decl, Void p) {
    if (decl.isInnerClass()) {
      this.classFQName += "." + decl.getName().toString();
    } else {
      if (!this.classFQName.equals("")) {
        throw new UnsupportedOperationException(
            "Attempted to enter an unexpected kind of class: "
                + decl.getFullyQualifiedName()
                + " but already had a set classFQName: "
                + classFQName);
      }
      // Should always be present.
      this.classFQName = decl.getFullyQualifiedName().orElseThrow();
    }
    Visitable result = super.visit(decl, p);
    if (decl.isInnerClass()) {
      this.classFQName = this.classFQName.substring(0, this.classFQName.lastIndexOf('.'));
    } else {
      this.classFQName = "";
    }
    return result;
  }

  @Override
  public Visitable visit(MethodDeclaration method, Void p) {
    String methodDeclAsString = method.getDeclarationAsString(false, false, false);
    // The substring here is to remove the method's return type. Return types cannot contain spaces.
    // TODO: test this with annotations
    String methodName =
        this.classFQName + "#" + methodDeclAsString.substring(methodDeclAsString.indexOf(' ') + 1);
    if (this.targetMethodNames.contains(methodName)) {
      insideTargetMethod = true;
      targetMethods.add(method.resolve().getQualifiedSignature());
      unfoundMethods.remove(methodName);
    }
    Visitable result = super.visit(method, p);
    insideTargetMethod = false;
    return result;
  }

  @Override
  public Visitable visit(MethodCallExpr call, Void p) {
    if (insideTargetMethod) {
      usedMethods.add(call.resolve().getQualifiedSignature());
    }
    return super.visit(call, p);
  }

  @Override
  public Visitable visit(ObjectCreationExpr newExpr, Void p) {
    if (insideTargetMethod) {
      usedMethods.add(newExpr.resolve().getQualifiedSignature());
    }
    return super.visit(newExpr, p);
  }
}
