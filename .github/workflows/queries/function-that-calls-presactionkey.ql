/**
 * @description Find functions that call press Actionkey
 * @kind problem
 * @id javascript/function-that-calls-presactionkey
 * @problem.severity recommendation
 */
import javascript

/**
 * Holds if a function is a test and if its pressActionKey
 */
predicate isTest(Function test) {
  exists(CallExpr describe, CallExpr it |
    describe.getCalleeName() = "describe" and
    it.getCalleeName() = "it" and
    it.getParent*() = describe and
    test = it.getArgument(1) and 
    it.getName() = "pressActionKey"
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
select callee, "is directly called by a test"
