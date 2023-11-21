/**
 * @description Find all files with extension "ts" or "tsx" that has comments
 * @kind problem
 * @id javascript/files-without-comments
 * @problem.severity recommendation
 */
import javascript

predicate isJavaScriptOrTypeScriptFile(File file) {
  file.getExtension() = "ts" or file.getExtension() = "tsx"
}

predicate doesNotContainComments(File file) {
  exists(Comment comment | comment.getFile() = file)
}

from File file
where isJavaScriptOrTypeScriptFile(file) and 
      doesNotContainComments(file)
select file, "Found file without comments: " + file.getAbsolutePath()
