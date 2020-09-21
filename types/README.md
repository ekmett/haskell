types
=====

This library provides a very fast notion of singleton types, a la `singletons`. The cost difference is
*O(1)* vs *O(n)* in the size of the term being lifted to the type level to perform a round-trip.

In addition, it uses various tricks to lower multiple kinds that previously did not have a term representation:

* `Type` look like `Data.Typeable.TypeRep`, while `Sing (a :: Type)` is effectively `Type.Reflection.TypeRep`

* `Constraint` look like an existentially quantified dictionary, while `Sing (a :: Constraint)` matches `Dict a`

* `Nat` can be used like `Natural`

* `Symbol` looks like `String`.

This makes makes working with singleton types much more uniform.

Finally, we allow lifting additional types, like `Int` and `Char`, even `Ptr` to the type level.

This makes type level programming and "mildly-dependent" Haskell much more uniform to work with
and avoid compromising efficiency.

License
-------

[Licensed](LICENSE.md) under either of

 * [Apache License, Version 2.0][license-apache]

 * [BSD 2-Clause license][license-bsd]

at your option.

Contribution
------------

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you shall be dual-licensed as above, without any
additional terms or conditions.

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the `#haskell` IRC channel on `irc.freenode.net`.

-Edward Kmett

 [license-apache]: http://www.apache.org/licenses/LICENSE-2.0
 [license-bsd]: https://opensource.org/licenses/BSD-2-Clause
