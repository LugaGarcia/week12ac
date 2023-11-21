/**
 * @description Find public methods called by tests
 * @kind problem
 * @id javascript/public-methods-called-by-tests
 * @problem.severity recommendation
 */
import javascript

/**
 * Holds if a function is a test.
 * And Public
 */
predicate isTest(Function test) {
  exists(CallExpr describe, CallExpr it |
    describe.getCalleeName() = "describe" and
    it.getCalleeName() = "it" and
    it.getParent*() = describe and
    test = it.getArgument(1)
    # will there be a identifier here for it to be public?
  )
}

/**
* Holds if `caller` contains a call to `callee`.
*/
predicate calls(Function caller, Function callee) {
  exists(DataFlow::CallNode call |
    call.getEnclosingFunction() = caller and
    call.getACallee() = callee
  )
}

from Function test, Function callee
where isTest(test) and
      calls(test, callee)
select callee, "is called by a test and is public"
