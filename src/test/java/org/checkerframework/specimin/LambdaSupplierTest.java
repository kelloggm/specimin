package org.checkerframework.specimin;

import java.io.IOException;
import org.junit.Test;

/**
 * This test checks that we can infer a type that's reasonable when a lambda is passed to a function
 * in a synthetic class.
 */
public class LambdaSupplierTest {
  @Test
  public void runTest() throws IOException {
    SpeciminTestExecutor.runTestWithoutJarPaths(
        "lambdasupplier",
        new String[] {"com/example/Simple.java"},
        new String[] {"com.example.Simple#bar(LambdaUser)"});
  }
}