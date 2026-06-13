 And then - let think about branch where opaque is left in walk_type_deep.  Maybe it means that we have wrong policy
  or wrong identity of RigidVar ? Or we should not use identity, but use something like
  alpha-equal thunk...?  Can you describe, how walk_type_deep is used, why opaque case is needed and lets brainstorm alternatives
