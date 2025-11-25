#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#show link: set text(blue)

#set heading(numbering: "1.1")

#align(center, text(size: 20pt, [*Typescript-like Types in Lean*]))

= Motiviation

When working with JSON Schema, either to do run-time validation or to autogenerate Lean `structure`s, constructing and working with JSON objects becomes cumbersome and difficult. For instance, many plotting
configs in VegaLite end up in the form:

```lean
structure Config where
  param1 : String ⊕ ExprRef
  param2 : Float ⊕ ExprRef
  param3 : Int ⊕ ExprRef
  ...
```

Constructing such objects would then require `.inl _` every time, which is annoying to use. Constructing
substructures requires remembering the names and structure of parameters which are unnecessary for 99% of use cases. Most plots do not need the "backdoor" into Vega that `ExprRef` allows you. One option would be to manually construct alternative types which have default coercions from `String`. However, there are 60,000 lines of VegaLite types, so an alternative target for automatic generation is quite attractive.

= Goals

We would like succinct typesafe JSON with TypeScript-like behavior in Lean.

- Capable enough schema description: intersections, unions, objects, literals, objects, arrays, etc.
- Runtime checking
- Natural JSON syntax
- Enable compile-time checking of automatically generated schemas.
- Propagate JSON type information for field-accessors, discriminant-based narrowing, and object construction.
- Subtyping relation
- (Optional) be able to convert from JSON Schema (however, maybe not the full spec yet)

= Non-goals

- Advanced typescript types: type parameters, conditional types, recursive types
- Compatability with Typescript
- Non-json types

= Alternatives Considered

- GADTs do not solve the problem of `.inl` everywhere and cannot represent type unions easily.
- Runtime type checking does not provide enough safety to guide use-cases like a large plotting library.

= General Approach

```lean
structure JsonType where
  | literal ...
  | inter ...
  | union ...
  | ...

-- Runtime checking
def JsonType.check (t : JsonType) (x : Json) : Bool := ...

-- TypedJson as Subtype
def TypedJson (t : JsonType) := Subtype (t.check · = true)
```

Assuming `schema` is a known constant, we can use that information using `decide` or `native_decide`. Using the proposition `schema.check obj = true`, then you can use various decidable facts to extract information:
- Given `schema.check obj = true`
- We check that `schema.hasField "param1" = true` and let `fieldType := schema.getField "param1"`
- Then `fieldType.check (obj.getObjVal! "param1") = true`.

Since `schema` will generally be available as a constant, we can compute information about it at compile-time using `decide`/`native_decide`.

== Other potentially pain points

- *Inference during construction*: It may be helpful to automatically assign types for simple constructions. It is not easy to make Json objects in Lean by default.
- *Accesing properties and indices*: Accessing properties of Json objects is already difficult right now. Maybe macros can include the necessary proof plumbing, so `typedJson @. param1` checks that `param1` is in the type.
- *Schema Construction*: Constructing a schema either automatically or even within Lean will likely be difficult.

= Type System

== Notation

#let nullLit = strong([null])
#let trueLit = strong([true])
#let falseLit = strong([false])

#let nullType = strong([null])
#let boolType = strong([bool])
#let stringType = strong([string])
#let numberType = strong([number])
#let anyType = strong([any])
#let neverType = strong([never])

$
  "JSON Values" quad v ::= nullLit | trueLit | falseLit | n | s | [v_1, ..., v_n] | {f_1: v_1, ..., f_n: v_n}
$

$
  "JSON Types" quad tau ::= nullType & | boolType | numberType | stringType | anyType \
                                     & | ("literal" :: "String") | ("number" :: "Nat") ... \
                                     & | {f_1 : tau_1, ..., f_n : tau_n, o_1 : sigma_1, ..., o_m : sigma_m} "(Object)" \
                                     & | [tau_1, ..., t_n] "(Tuple)" \
                                     & | tau[] "(Array)" \
                                     & | (tau_1 | tau_2) "(Union)" \
                                     & | tau_1 \& tau_2 "(Intersection)" \
                                     & | neverType
$

== Type Checking <type-checking>

/*
#let tree = rule(
  label: [Label],
  name: [Rule name],
  [Premise 1],
  [Premise 2],
  [Premise 3],
  [Conclusion],
)

#prooftree(tree)
*/

We will denote Lean typing as $s :: "String"$, which will be rarely used. While we will use $s : stringType$ to indicate typing in our subtype system `stringType.check s = true`.

=== Basic Types and Literals

$
  prooftree(rule(nullLit : nullType,)) quad
  prooftree(rule(trueLit : boolType,)) quad
  prooftree(rule(falseLit : boolType,)) quad
  prooftree(rule(name: "fromString", s :: "String", s : stringType,)) quad \
  prooftree(rule(name: "fromNat", i :: "Nat", i : numberType,)) quad
  prooftree(rule(name: "fromInt", i :: "Int", i : numberType,)) quad
  prooftree(rule(name: "fromFloat", i :: "Float", i : numberType,))
$

*Literals*

$
  prooftree(rule(s : (s :: "String"))) quad
  prooftree(rule(x : (x :: "Nat"))) quad
  prooftree(rule(x : (x :: "Int"))) quad
  prooftree(rule(x : (x :: "Float")))
$

*any*

$
  prooftree(rule(v : anyType))
$

=== Schema combinators

*Arrays*

$
  prooftree(
    rule(
      v_i : tau, ..., v_n : tau,
      [v_1, ..., v_n] : tau[]
    )
  )
$

*Tuples*

$
  prooftree(
    rule(
      v_i : tau_1, ..., v_n : tau_n,
      [v_1, ..., v_n] : [tau_1, ... tau_n]
    )
  )
$

*Unions*

$
  prooftree(
    rule(
      v : tau_1,
      v : tau_1 | tau_2
    )
  ) quad
  prooftree(
    rule(
      v : tau_2,
      v : tau_1 | tau_2
    )
  )
$

*Intersections*

$
  prooftree(
    rule(
      v : tau_1, v : tau_2,
      v : tau_1 \& tau_2
    )
  )
$

*Objects*

Note that ${}$ should be taken to be unordered. For notation, $o_i$ are the optional field names,
$w_i$ the optional values, and $sigma_m$ the optional types.
heading
$
  prooftree(
    rule(
      v_1 : tau_1, ..., v_n : tau_n, w_(i_1) : sigma_(i_1), ..., w_(i_k) : sigma_(i_k),
      {f_1 : v_1, ..., f_n : v_n, o_(i_1) : w_(i_1), ..., o_(i_k) : w_(i_k)} :
      {f_1 : tau_1, ..., f_n: tau_n, o_1? : sigma_1, ..., o_n : sigma_n}
    )
  )
$

This formulation does not require $k$ to be positive, and it implies some sort of subtyping to be consistent.

== Subtype Checking

Even if we know that $v : tau_1$ as a hypothesis, we may be unable to pass it safely to a function that
takes $tau_2$. We need a way to reliable coerce values during compile time. We can implement this
with a decidable subtyping relation $<:$ which is proven true.

So if $v : tau_1$ implies $v : tau_2$, then this will not imply that $tau_1 <: tau_2$, so subtyping is complete. Rather, we'll target a subset of easily checkable rules so that $tau_1 <: tau_2$ and
$v : tau_1$ imply that $v : tau_2$.

As in type checking, the judgements below show how the algorithm works. We will recursively check different conditions, moving up the tree, and backtracking if necessary.

*Trivial subtyping*
$
  prooftree(rule(tau <: tau)) quad
  prooftree(rule(tau <: anyType)) quad
  prooftree(rule(neverType <: tau))
$

*Arrays*

$
  prooftree(
    rule(
      tau_1 <: tau_2,
      tau_1[] <: tau_2[]
    )
  )
$

*Tuples*

$
  prooftree(
    rule(
      tau_1 <: tau, ..., tau_n <: tau,
      [tau_1, ..., tau_n] <: tau[]
    )
  ) quad
  prooftree(
    rule(
      tau_1 <: sigma_1, ... tau_n <: sigma_n,
      [tau_1, ... tau_n] <: [sigma_1, ... sigma_n]
    )
  )
$

*Unions*

$
  prooftree(
    rule(
      tau <: tau_1,
      tau <: tau_1 | tau_2
    )
  ) quad
  prooftree(
    rule(
      tau <: tau_2,
      tau <: tau_1 | tau_2
    )
  )
$

*Intersection*

$
  prooftree(
    rule(
      tau <: tau_1, tau <: tau_2,
      tau <: tau_1 \& tau_2
    )
  ) quad
  prooftree(
    rule(
      tau_1 <: tau,
      tau_1 \& tau_2 <: tau
    )
  ) quad
  prooftree(
    rule(
      tau_2 <: tau,
      tau_1 \& tau_2 <: tau
    )
  )
$

*Literals*

Literal types are subtypes of their base types:

$
  prooftree(rule(("string literal" s) <: stringType)) quad
  prooftree(rule(("number literal" n) <: numberType)) quad
  prooftree(rule(("bool literal" b) <: boolType))
$

*Objects*

For objects with required and optional fields, we write $v_1 = {f_1 : tau_1, ..., f_n: tau_n, o_1? : sigma_1, ..., o_m? : sigma_m}$ where $f_i$ are required and $o_i$ are optional.

For all required fields in $tau_2$, they must be required in $tau_1$ with a subtype. For all optional fields in $tau_2$, they must exist (either as required or optional) in $tau_1$ with a subtype.

$
  prooftree(
    rule(
      forall f_i in tau_2."required" \, f_i in tau_1."required" and tau_1.f_i <: tau_2.f_i,
      forall o_i in tau_2."optional"\, o_i in (tau_1."required" union tau_1."optional") and tau_1.o_i <: tau_2.o_i,
      tau_1 <: tau_2
    )
  )
$

This ensures width subtyping (extra fields allowed in $tau_1$) and depth subtyping (covariant field types), while preventing incompatible types for shared fields.

*Soundness note*: The second condition is critical for soundness with open objects. Without it, ${} <: {x? : "string"}$ would hold, but an object satisfying ${}$ could have ${x: 42}$ which violates ${x? : "string"}$.

The subtyping is also similar to record subtyping as in #link("https://softwarefoundations.cis.upenn.edu/plf-current/Sub.html", [Software Foundations subtyping section]).

=== Normalization

We will also need various normalization procedures, which will only be applied once, that will make subtyping more powerful.

*Key lemma:* Normalization must preserve the set of values that check against a type:

$
  ("norm" tau)."check"(v) arrow.l.r.double tau."check"(v)
$

This equivalence is critical for the soundness of using normalization as a preprocessor:

$
  prooftree(
    rule(
      norm tau_1 <: norm tau_2,
      tau_1 <: tau_2
    )
  )
$

*Literals*
$
  nullType mapsto nullType,
  boolType mapsto boolType,
  numberType mapsto numberType,
  stringType mapsto stringType,
  anyType mapsto anyType,
  neverType mapsto neverType
$

*Objects*

Objects fields should be sorted and all optional fields $o_i$ should be separate.

$
  {f_1 : tau_1, ..., f_n : tau_n, o_1 : sigma_1, ..., o_m : sigma_m} mapsto
  {f_1 : norm tau_1, ..., f_n : norm tau_n, o_1 : norm sigma_1, ..., o_m : norm sigma_m}
$

*Tuples*

$
  [tau_1, ... tau_n] mapsto [norm tau_1, ..., norm tau_n]
$

*Arrays*

$
  tau[] mapsto (norm tau)[]
$

*Unions and Intersections*

$
  tau_1 | tau_2 mapsto (norm tau_1) | (norm tau_2) quad
  tau_1 \& tau_2 mapsto (norm tau_1) \& (norm tau_2)
$

All $n$-length unions and intersections should be sorted, and the formulas should be put into
disjunctive normal form (this is to enable narrowing later):
$
  tau_1 \& (tau_2 | tau_3) mapsto (tau_1 \& tau_2) | (tau_1 \& tau_2)
$

Shared fields in intersections should be merged and extra fields should be concatenated:
$
  {f_1 : tau_1, ..., f_n : tau_n, ...} \& {f_1 : sigma_1, ... f_n : sigma_n, ...} mapsto
  {f_1 : tau_1 \& sigma_1, ..., f_n : tau_n \& sigma_n, ...}.
$

*Never*

Every #neverType in a union should be removed. A single #neverType in a tuple, array, or intersection should turn the whole type into #neverType. A #neverType in the required params of an object type should turn to #neverType, while optionals should be removed.

= Type "Inference"

== Making objects

Given known objects, it may be appropriate to use the type rules in #ref(<type-checking>) for real construction:
- We should able to construct a typed null, typed objects, etc.

This mirrors more directly a GADT approach.

== Accessing fields

Just as almost all languages provide the ability to type access of structures and arrays, so `x.property` has a known type, we need to be able to provide types easily for accessed properties.

Since we can always decide whether $tau <: {f : sigma}$ and in fact, we can _get_ $sigma$
using a function $"fieldType" tau$, we need only work with known ${f : sigma}$. In this case,
we only need to prove

$
  prooftree(rule(v : {f : tau}, v.f : tau))
$

== Narrrowing

In typescript, one central part of typing is how to discriminate unions. Unlike many other languages with
similar features, tags are relatively easy to apply. Typescript calls this #link("https://www.typescriptlang.org/docs/handbook/2/narrowing.html", [narrowing]).

```typescript
function padLeft(padding: number | string, input: string): string {
  if (typeof padding === "number") {
    return " ".repeat(padding) + input;
    // padding: number
  }
  return padding + input;
  // padding: string
}
```

Typescript will automatically apply narrowing across controw-flow for
- `typeof obj === "number`
- `obj instanceOf Supertype` (this one will turn into intersection)
- `shape.kind === "rect"`
- `x === y`
- `"swim" in animal`

In Lean terms, we can implement this by using macros which inspect the available context instead of analyzing control-flow. We can construct specific types that look for these hypotheses when
trying to infer a type. Like subtyping, these rules are search paths which are proven correct. Unlike subtyping, we will be trying to produce the $tau$ in the conclusion, so these are _forward_ rules instead of _backward_ rules. Unfortunately, these are far more likely to end up as macros, since requirements for each rule are in the Lean context.


$
  prooftree(
    rule(
      "typeof" v = tau,
      v : tau
    )
  ) quad
  prooftree(
    rule(
      v : tau_1, v : tau_2,
      v : tau_1 \& tau_2
    )
  ) quad
  prooftree(
    rule(
      "v.f = value",
      v : {f : "value"}
    )
  )
  prooftree(
    rule(
      "v = w", v : tau_1, w : tau_2,
      v : tau_1 \& tau_2
    )
  )
  prooftree(
    rule(
      "f in v",
      v : {f : anyType}
    )
  )
$

Since types are expected to always be in context, intersections are expected to normalize to much
more convenient types.

= Potential Extra Conveniences

- Being able to turn JSON Schema into such types
- Additional type constructors
- Convenient syntax (also for JSON objects and typed JSON objects). The current notation is bad.
- Convenient special macros to do the above algorithms, instead of merely proofs. Perhaps `simp` sets, `grind` rules, or `aesop` collections.

= Side note on Flow Typing

Whenever you have a single type which will be used in many different ways, this is a "convenient" way to
get flow-sensitive typing.

Your set of properties _should_ form a lattice, which makes this especially convenient, and there
are even ways to handle recursion by using fixed-point theorems in lattice theory.

After reading #link("https://ayazhafiz.com/articles/22/why-dont-more-languages-offer-flow-typing", [Why Don't More Languages Offer Flow Typing]), I became aware that I really want _flow types_ defined
over any lattice.

Given Lean's pseudo-SMT solver `grind`, combining and constructing little flow types for a type could be very easy. As an example, perhaps row-types or dataframes are best implemented in this way.
