/-
Compatibility shims for the comparator kernel-builtin export list.

`comparator` (Lean FRO) asks `lean4export` for a fixed list of kernel
builtin constants. Two names on that list, `String.ofList` and
`eagerReduce`, only exist in Lean >= 4.16 / >= 4.13 kernels and are
absent from this project's Lean v4.11.0 environment. This module
defines inert stand-ins with those exact names so that the export
requested by the *unmodified* comparator binary succeeds.

Both `Hardening.Challenge` and `Hardening.Solution` import this file,
so the stand-ins are byte-identical in both exports. They are ordinary
safe definitions, are compared like every other shared constant, and
participate in the kernel replay. No theorem below uses them.
-/

/-- Stand-in for the Lean >= 4.16 alias of `String.mk`. -/
def String.ofList (data : List Char) : String := ⟨data⟩

/-- Stand-in for the Lean >= 4.13 kernel constant `eagerReduce`. -/
def eagerReduce (n : Nat) : Nat := n
