*Issue #, if available:*

*Description of changes:*

*Squash/merge commit message, if applicable:*


By submitting this pull request, I confirm that my contribution is made under the terms of the Apache 2.0 license.

# Due to [dafny-lang/dafny#2500](https://github.com/dafny-lang/dafny/issues/2500), Traits are dangerous:
1. [ ] Does this PR add any traits or classes that extend a trait?
2. [ ] Are these traits annotated with `{:termination false}`?

The override checks on 
the specifications on
a class' functions/methods/etc. validating
that specifications are 
at least as strong as those on
the traits it implements
are not working correctly when 
that trait is defined in a different module 
(and hence must have `{:termination false}` on it).

As such, if either (1.) or (2.) is true:
Have you [ ] manually verified all the trait specifications are copied onto classes that extend them?
