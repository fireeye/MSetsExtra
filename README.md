# Efficiently Executable Sets Library

Coq (as of version 8.4pl6) provides the module `MSetInterface` which
contains interfaces for sets. There are implementations using sorted
and unsorted lists (both without duplicates) as well as AVL and RBT
trees for these interfaces. While these implementations - particularly
the ones based on binary trees - extract to reasonably efficient code,
at FireEye we nevertheless were struggling with performance
issues.

This directory contains extensions to Coq's set library that helped
us, i.e. the FireEye Formal Methods team (formal-methods@fireeye.com),
solve these performance issues.

There are the following files

- `MSetWithDups.v` (interface definitions for `MSetListWithDups.v`)
- `MSetListWithDups.v` (unsorted Lists with duplicates)
- `MSetIntervals.v` (sets implemented as intervals of integers)
- `MSetFoldWithAbort.v` (efficient fold operation)

- `readme.md` (this readme)
- `LICENSE` (license information, LGPL 2.1)
- `configure.sh` 
- `_CoqProject` 
- `Makefile` 
- `doc/*` (high level documentation)


The `Makefile` is generated via `coq_makefile` from `_CoqProject`. This
is performed by `configure.sh`.

## OPAM

This library is available as an opam package as `coq-msets-extra`. In
order to use it, add the coq opam repository

	opam repo add coq-released https://coq.inria.fr/opam/released
	opam update

Afterwards you can install this libaray via

	opam install coq-msets-extra

## Interval Sets

The file `MSetIntervals.v` contains an implementation of `WSetOn`,
which is backed by a sorted list of integer intervals. It is very
space efficient for large sets that can be represented by a small
number of large intervals.  There are instantiations of this set for
the element types `Z`, `N` and `nat`.  Further instantiation can be
easily created by the user.


## Unsorted Lists With Duplicates 

The file `MSetListWithDups.v` contains an implementation of sets as
unsorted lists with duplicates. It has has an O(1) `add` operation and
an O(n) `union` operation. The price for this is that we allow duplicates
and `fold` is allowed to visit elements multiple times. It is the users 
responsibility to use this set implementation carefully and avoid adding
the same element over and over again. Otherwise, a lot of space is used and
performance of operations like `filter` might become arbitrarily bad.

Since `fold` is allowed to visit elements multiple times, this set
implementation cannot instantiate the standard weak set interfaces
(e.g. `WSetOn`). Therefore, the file `MSetWithDups.v` provides
specialized interfaces for it and establishes the connection of these
interfaces with `WSetOn`.


## Fold With Abort

Folding over all elements of a set is a core operation, which has
close ties to the concept of iterators in languages like C++. However,
while iterators allow early abort, this is not possible with
the standard fold operation. As a result, many efficient iterator
algorithms become inefficient when implemented via folding.

_Fold with abort_ operations are an
answer to this issue.  `MSetFoldWithAbort.v` provides interfaces for a family of such
fold with abort operations and use these operations to define operation like a
very efficient filter or existence check. The interfaces
are instantiated for all of Coq's current set implementations, i.e. for
AVL trees, RBT trees, sorted lists and unsorted lists without duplicates.
_Fold with abort_ can exploit the binary tree structure. Therefore the binary
search tree implementation can skip the most work. Sorted lists are good as well,
since the ordering can be used for aborting. For unsorted lists, operations like
`filter` are not optimized, but at least operations like existence checks can
abort early.
