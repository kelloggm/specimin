package org.checkerframework.specimin;

import java.io.IOException;
import org.junit.Test;

/** This test checks that Specimin preserves the right constructors in a constructor chain. */
public class ConstructorChainingTest {
  @Test
  public void runTest() throws IOException {
    SpeciminTestExecutor.runTestWithoutJarPaths(
        "constructorchaining",
        new String[] {"com/example/Simple.java"},
        new String[] {"com.example.Simple#bar()"});
  }
}
