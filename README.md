# Colean

(Co)inductive types for Lean 4.

Lean has coinductive predicates (`coinductive`, in `Prop`), but no coinductive data types.
Colean adds the `codatatype` command that declares them, with `inductive`-like syntax.

```lean
/-- Potentially infinite lists -/
codatatype CoList (α : Type)
  | nil
  | cons (head : α) (tail : CoList α)
```

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Colean"
git = "https://github.com/verse-lab/colean"
rev = "main"
```

Then `import Colean`.

## Examples

### Coinductive types

```lean
/-- Infinite lists -/
codatatype Stream (α : Type)
  | cons (head : α) (tail : Stream α)

def Stream.map {α β : Type} (f : α → β) : Stream α → Stream β :=
  -- `corec` defines a corecursive function
  Stream.corec fun s : Stream α =>
    -- to pattern match, first apply the destructor `dtor`
    match s.dtor with
    | .cons h t => .cons (f h) t

-- Coinduction: bisimilar streams are equal
theorem Stream.map_comp {α β γ : Type} (f : α → β) (g : β → γ) (s : Stream α) : 
    s.map (g ∘ f) = (s.map f).map g := by
  refine Stream.bisim (fun lhs rhs => ∃ s, lhs = s.map (g ∘ f) ∧ rhs = (s.map f).map g)
    ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  -- coinductive step
  cases s with | cons h t => -- `cases` works with `codatatype`
  simp [map]
  exists t
```

### Corecursion by `partial_fixpoint`

An easier way to define corecursive functions is Lean's `partial_fixpoint`:

```lean
/-- Potentially infinite lists -/
-- `with_ccpo` creates a CCPO structure, which `partial_fixpoint` uses
@[with_ccpo (bot := nil)] -- `bot` chooses the bottom `⊥` of the CCPO; it can be omitted here
codatatype CoList (α : Type)
  | nil
  | cons (head : α) (tail : CoList α)

def nats (n : Nat) : CoList Nat :=
  .cons n (nats (n + 1))
partial_fixpoint

def CoList.filter {α : Type} (p : α → Bool) (s : CoList α) : CoList α :=
  match s.dtor with
  | .nil => .nil
  | .cons h t => if p h then .cons h (t.filter p) else t.filter p
partial_fixpoint

example : (nats 0).filter (· % 2 == 0) = .cons 0 ((nats 2).filter (· % 2 == 0)) := by
  repeat
    rw [CoList.filter, nats]; simp
```

### Indexed families

```lean
/-- Infinite walk starting from `n` -/
codatatype Walk : Int → Type
  | up {n : Int} (tail : Walk (n + 1)) : Walk n
  | down {n : Int} (tail : Walk (n - 1)) : Walk n

-- The step may depend on the index: always head back to `0`.
def Walk.toZero {n : Int} : Walk n :=
  .corec (s := ()) fun (n : Int) (_ : Unit) =>
    if n < 0 then .up () else .down ()

/-- A helper for the next definition -/
def Walk.cast {m n : Int} (h : m = n) (w : Walk m) : Walk n := h ▸ w

-- The state may depend on the index: a walk from `-i` is the state at `i`.
def Walk.mirror {n : Int} (w : Walk n) : Walk (-n) :=
  .corec (S := fun i => Walk (-i))
    (fun _ w => match w.dtor with
      | .up t => .down (t.cast (by lia))
      | .down t => .up (t.cast (by lia)))
    (w.cast (by lia))
```

### Mutual blocks

```lean
mutual
/-- Trees of any depth and any breadth. -/
codatatype Tree (α : Type)
  | node (a : α) (children : Forest α)
/-- Sequences of trees, possibly infinite. -/
codatatype Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

-- Corecursion with one state and one step per type: the infinite binary tree.
-- A forest's state counts the trees still to come.
def Tree.binary {α : Type} (a : α) : Tree α :=
  -- .node a (.cons binary (.cons binary nil))
  Tree.corec (fun () => .node a (2 : Fin 3)) (fun | 0 => .nil | 1 => .cons () 0 | 2 => .cons () 1) ()

theorem Tree.binary_eq {α : Type} (a : α) : 
    binary a = .node a (.cons (binary a) <| .cons (binary a) <| .nil) := by
  conv => lhs; rw [binary, Tree.corec_eq]
  simp [Forest.corec_eq]
  rfl
```

### Nesting

```lean
/-- Nondeterministic computations: a result, or a finite choice of ways to continue. -/
codatatype NDet (α : Type)
  | ret (a : α)
  | choose (next : List (NDet α)) -- nesting through `List`

def NDet.coin : NDet Bool := .choose [.ret false, .ret true]

/-- Flip coins until one shows `true`, counting the flips: stop now, or flip again. -/
def NDet.flips : NDet Nat :=
  NDet.corec (S := Nat ⊕ Nat) (s := .inr 0) (fun
    | .inl n => .ret n
    | .inr n => .choose [.inl (n + 1), .inr (n + 1)]) 

-- One can nest through a predefined set of standard Lean types (`Prod`, `Sum`, `List`, `Option`,
-- etc.) and through types defined with `codatatype` and `datatype` (see below).
```

### Inductive types

Inductive types are declared with `datatype`. They can also be in a `mutual` block and used in
nesting.

```lean
datatype LogicalFormula
  | const (b : Bool)
  | and (x y : LogicalFormula)
  | or (x y : LogicalFormula)
  | not (x : LogicalFormula)
```

### Mixed blocks

Finally, `datatype` and `codatatype` can be mixed in a `mixed_mutual` block:

```lean
mixed_mutual
/-- Stream processors: they keep producing outputs forever... -/
codatatype SP (I O : Type)
  | step (s : Step I O)
/-- ...and read finitely many inputs before each output. -/
datatype Step (I O : Type)
  | get (k : I → Step I O)
  | put (o : O) (next : SP I O)
end

/-- Read two inputs, output their sum, forever. -/
def SP.pairSums : SP Nat Nat :=
  .corec (s := ()) fun _ => .step (.get fun a => .get fun b => .put (a + b) ()) 
```

It is important to note that `mixed_mutual`, unlike a uniform `mutual`, depends on the order of
the types. Types are defined bottom-up, each treating the types above it as placeholders. So
`datatype Step` only makes the reads up to the next `put` finite, while `codatatype SP` lets the
processor as a whole run forever. In the reverse order, `SP I O` would be empty: the whole
processor would have to be finite, but nothing ever ends it.

## How it works, and why you can trust it

The project was developed with heavy use of AI, but it is designed so that the trusted code base
(TCB) grows very little.

A declaration of a type `T` is processed in four steps.

1. **The functor.** We start from the syntax of your declaration and generate a functor `T.F`:
   an ordinary `inductive` with the same constructors, where every occurrence of `T` is
   replaced by a variable `X`, together with its action on functions `T.F.fmap`. The code that
   does this is small, [`Colean/Gen/Functor.lean`](Colean/Gen/Functor.lean), and you can read
   its output directly:

   ```
   #print Stream.F
   -- Stream.F.cons : {α : Type} → {X : Type u_1} → α → X → Stream.F α X
   #print Stream.F.fmap
   -- fun f a => Stream.F.casesOn a fun head tail => Stream.F.cons head (f tail)
   ```

2. **The type.** `T` is built as a subtype of a general carrier, a least or greatest fixpoint
   of an encoding of `T.F`. This is the large and heavy part, and nobody needs to review it,
   because of the next step.

3. **The contract.** Colean proves `T.contract : Codata.Contract T T.F` (or
   `Data.Contract` for `datatype`), defined in [`Colean/Framework.lean`](Colean/Framework.lean).
   For `codatatype`, the contract asks for a destructor `dtor : T → T.F T`, a corecursor with its
   computation rule `dtor (corec c s) = T.F.fmap (corec c) (c s)`, and the coinduction principle
   for the relation lifting `Rel`. `Rel` is defined once in the same file from `map` alone: it
   is not something the generator can choose. This says exactly that `T` is the final
   coalgebra of `T.F`. Any two types with a contract for the same functor are isomorphic
   (`Codata.Contract.corec_corec`). Dually, `Data.Contract` asks for a constructor, a fold with
   its computation rule, and induction, and says that `T` is the initial algebra of `T.F`.

4. **The interface.** Everything else is derived from the contract.
   - [`Colean/Framework.lean`](Colean/Framework.lean) holds the general theorems: the
     constructor as the inverse of the destructor (Lambek's lemma), injectivity, and uniqueness
     of `corec` and `fold`.
   - [`Colean/Gen/Framework.lean`](Colean/Gen/Framework.lean) instantiates them for `T` and
     contains no proofs of its own.
   - [`Colean/Gen/Surface.lean`](Colean/Gen/Surface.lean) builds the user-facing declarations
     from these pieces. A constructor is the contract's constructor at the functor's
     constructor (`#print Stream.cons` shows `Stream.ctor (Stream.F.cons head tail)`), and
     `casesOn` is case analysis on `dtor`.

   The dependent recursor `T.rec` of a `datatype` is built on the encoding, but its type and
   its computation rules `T.rec_cᵢ`, which are theorems, say what it is.

So the TCB consists of three pieces: the functor extraction, the definition of the
contract, and the derivation of the interface. To check a declared type, it is then enough to
look at its functor and its contract (`#print T.F`, `#check @T.contract`).

A `mutual` block is one family indexed by which type you mean, `Tree_Forest.Ix`, with one
contract for the block, and each type is that family at its index
(`#print Tree` shows `Tree_Forest Tree_Forest.Ix.Tree`). In a `mixed_mutual` block, an inner
type is first declared with the outer types as a parameter (`Step.Open I O X`), with its own
contract, and the closed type is that one at the outer type (`Step I O := Step.Open I O (SP I O)`).

Colean does not handle every declaration you can write: it supports most of the types that are
useful in practice, and it may reject some it could in principle accept. When it cannot build
a type or prove its contract, the command fails with an error and declares nothing. It never
produces a type that does not satisfy its contract. Bug reports and feature requests are welcome
in the [issues](https://github.com/verse-lab/colean/issues).

## Limitations

- **No coinduction tactic and no general corecursion.** Coinduction is by applying `T.bisim`
  with a relation you write. Corecursion is primitive, through `T.corec`, or through
  `partial_fixpoint` for a type with `with_ccpo`. There is nothing like Isabelle's
  `coinduction` proof method or its framework for corecursion up to friendly operations.
- **No `match` on the declared types.** The types are subtypes and their constructors are
  definitions, so `match`, `rcases` patterns, structural recursion and the equation compiler
  cannot see them. Use `casesOn`, `rec`, `fold`, `corec`, the `cases` and `induction` tactics
  (which use the generated eliminators), or `match t.dtor with`, which is a match on the
  functor, an ordinary inductive type. Lean's
  [RFC: custom recursors (lean4#2716)](https://github.com/leanprover/lean4/issues/2716) would
  lift this restriction.
- **Everything is noncomputable.** The generated types and functions cannot be run with `#eval`
  or compiled, so definitions that use them must be marked `noncomputable`. We plan to lift this
  in the future.
- **`mixed_mutual` is best effort.** It is supported only partly. An outer type with indices
  or an outer `mutual` block is not supported, and some blocks fail with errors that are hard
  to read.
- **Computation rules are theorems.** `rec`, `fold` and `corec` compute on constructors by
  `simp` lemmas (`T.rec_cᵢ`, `T.fold_cᵢ`, `T.dtor_corec`), not by definitional unfolding, so
  `rfl` and `decide` do not evaluate them.
