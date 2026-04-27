# Graph examples manual

This manual gives small, text-rendered graph examples for readers who want an
intuition before reading the Lean proofs. A plain edge is shown as `--`; a wrap
edge is shown as `==`.

## Example 1: one vertex, no edges

```text
v
```

- Connected components: `1`
- Balanced components: `1`
- Flat kernel dimension: `2`
- Möbius kernel dimension: `1 + 1 = 2`

There is no cycle and therefore no non-trivial wrap holonomy.

## Example 2: path with a wrap edge

```text
a == b -- c
```

- Connected components: `1`
- Balanced components: `1`
- Flat kernel dimension: `2`
- Möbius kernel dimension: `1 + 1 = 2`

A tree has no cycle obstruction. Wrap labels can be switched away along a
spanning tree, so the component remains balanced.

## Example 3: triangle with one wrap edge

```text
      a
     / \
    /   ==
   b --- c
```

- Connected components: `1`
- Balanced components: `0`
- Flat kernel dimension: `2`
- Möbius kernel dimension: `1 + 0 = 1`

The unique cycle has odd wrap parity, so the signed branch has no zero mode on
this component.

## Example 4: triangle with two wrap edges

```text
      a
     / \
    ==  ==
   b --- c
```

- Connected components: `1`
- Balanced components: `1`
- Flat kernel dimension: `2`
- Möbius kernel dimension: `1 + 1 = 2`

The cycle has even wrap parity, so the component is balanced.

## Example 5: disconnected mixed graph

```text
a == b -- c        x == y
 \       /          \  /
  -------            z
```

Read the left component as balanced if its closed cycles have even wrap parity,
and the right triangle as unbalanced if exactly one of its three edges is a wrap
edge.

- Connected components: `2`
- Balanced components: `1`
- Flat kernel dimension: `2 · 2 = 4`
- Möbius kernel dimension: `2 + 1 = 3`

This is the main counting pattern: every component contributes one scalar zero
mode, and only balanced components contribute a signed zero mode.

## How to use these examples with the Lean project

- Use the examples as intuition for the definitions in
  `ConnectionLaplacian/L6_Cohomology.lean`.
- Compare the counting statements with the recognition results in
  `ConnectionLaplacian/L8_Recognition.lean`.
- Treat the diagrams as explanatory documentation only; they are not separate
  Lean fixtures.

