package org.checkerframework.specimin;

import java.io.IOException;
import org.junit.Test;

/**
 * This test checks that if Specimin will work properly where there is a super constructor while the
 * parent class file is not in the root directory physically
 */
public class SyntheticAnnotationsTest {
  @Test
  public void runTest() throws IOException {
    SpeciminTestExecutor.runTestWithoutJarPaths(
        "syntheticannotations",
        new String[] {"com/example/Simple.java"},
        new String[] {"com.example.Simple#baz(String)"});
  }
}
