# External Soundness

## Background

We are in the process of building multiple implementations of the AWS Encryption SDK (ESDK) for multiple programming languages in 2020. Our implementation strategy is to implement the majority of the library in Dafny, with a minimal shim of code in each target language to wrap the Dafny implementation with a safe and relatively idiomatic API.

This is somewhat uncharted territory for Dafny: it has excelled for years at verifying properties of entirely self-contained Dafny programs, especially in an educational context, but this is one of if not the first case of releasing production software based on it. Although Dafny includes an `{:extern}` attribute that enables external code to link with Dafny in various contexts, it introduces potential unsoundness if the external code does not actually match the Dafny specification. To date, the attribute has largely been used to include trusted internal implementations, so the risk and impact of unsoundness has been somewhat minimized. Our project, however, must allow for customer code to both invoke Dafny code and implement Dafny extension points.

The impact of unsoundness becomes severe in this case. If a Dafny method declares a parameter of type `Foo`, for example, where `Foo` is a Dafny class, then Dafny will not allow passing a `null` value as an argument. Once this method is compiled to a target language such as C#, however, C# will allow `null` to be passed. This can lead to errors and undefined behaviour deep within the Dafny runtime, potentially far from the source of the error if the `null` value is stored and referenced at a later time. These issues will lead to a bad customer experience as it will not be clear that their code is at fault, which in turn will lead to increased operational load for our team in order to support such customers. It also undermines customer trust to tout the advantages of applying formal verification to our code base, only to ship bugs in the shim code.

Note that this problem is not unique to the ESDK, and I intend to present a large subset of this design to the Dafny community in the form of one or more RFCs, in order to motivate the Dafny changes that will be necessary to support this solutino.

## Requirements

1. The Dafny compiler should reject unsound programs involving external declarations by default as much as possible.
1. It must be possible to attach unproven assumptions to external code. The fact that these assumptions are unproven should be as explicit as possible, to aid in understanding and tracking potential technical debt.
1. We should aim to minimize the amount of manual shim code we have to write in each target language, as this directly affects the scalability of our approach.
1. The errors we provide to customers when their code violates requirements should be as clear as possible, ideally allowing them to understand the error by only referring to the target language API documentation and not the underlying Dafny source code.
1. (Nice to have) We would be happier with a solution that allows us to separate Dafny and target language source code cleanly, such that the latter can be developed, tested and built with standard tooling for each language.

This document uses a "List" datatype as a running example for the various requirements and options. It is a generalization of the `seq<T>` built-in Dafny datatype, supporting values that may exist on the heap. The initial definition below assumes it is immutable, although we will consider the implications of allowing mutation later on. It uses a 64-bit integer for length and a 8-bit integer for values, to provide common concrete types for external implementations.

```dafny
const twoToThe8 := 0x1_00
newtype uint8 = x | 0 <= x < twoToThe8

const twoToThe64 := 0x1_0000_0000_0000_0000
newtype uint64 = x | 0 <= x < twoToThe64

trait List {
  ghost const values: seq<uint8>
  predicate Valid()
    ensures Valid() ==> |values| < twoToThe64

  function method Length(): uint64
    requires Valid()
    ensures Length() == |values| as uint64
  
  method Get(i: uint64) returns (res: uint8)
    requires Valid()
    requires 0 <= i < Length()
    ensures res == values[i]
}
```

## Out of Scope

It has actually been difficult to exclude any issues as out-of-scope, because this is such a widely cross-cutting concern.

## Issues and Alternatives

The `{:extern}` attribute is currently quite overloaded. It can be applied to modules, traits, classes, methods and functions, and in most cases its effect is only to ensure that the names of these elements are preserved by the compiler, so that external code can reference them in some way. The details of how Dafny-generated code and manually-written external code are combined is largely left up to the specific target language. See Dafny GitHub issue [#469](https://github.com/dafny-lang/dafny/issues/469) for details.

We should first distiguish between two different use cases for linkage with external code, for the sake of consistent terminology:

1. *Exposed* methods, referring to methods that external code is able to invoke.
1. *Native* methods, referring to methods that may be implemented in external code.

In practice, it is difficult if not impossible to ensure that a method can be implemented in external code yet not invoked from external code. For example, it is natural for a Dafny code base to define a trait that is compiled to a C# interface, which can then be implemented using a C# class. There is nothing to stop other C# client code from creating this class and invoking its methods. In addition, there will be frequent use cases for methods that need to support both external invocation and native implementations anyway, such as the `List` example in this doc. Therefore, we propose focussing on this use case first. This is a two-way door: we can always support sound external-only or native-only methods in a future release of Dafny with looser restrictions, if this turns out to be strongly desired.


Most soundness issues can be addressed by forbidding all elements of Dafny method declarations that cannot be directly compiled to elements in the target language, as shown below. For all these constraints, we can take the approach of applying them to the ESDK code base while in parallel modifying the Dafny compiler to enforce them.

1. **Disallow types not directly supported by the target language/runtime**. This includes not only most subtypes but also `newtype` declarations that do not match a built-in type such as `int` exactly. Allowing a bounded type such as `newtype MyType = x | -100 <= x < 0x8000_0000` that compiles to a type such as `int` still introduces unsoundness, since external code could return `-1000`.

2. **Require all reference types used as in or out parameters are nullable (i.e. `Foo?` rather than just `Foo`)**. This is a corrolary of the previous statement, since many reference types in Dafny source code are implicitly non-null subtypes.

3. **Disallow almost all preconditions and postconditions.** The biggest threat to soundness is that most Dafny guarantees are checked statically. A fundamental feature of Dafny is pre- and post-conditions, expressed using `requires` and `ensures` declarations respectively. Currently, external methods may be invoked without necessarily satisfying their pre-conditions ([#461](https://github.com/dafny-lang/dafny/issues/461)) and the implementation of native methods may not necessarily satisfy their post-conditions ([#463](https://github.com/dafny-lang/dafny/issues/461)).



### External Invariants

The attentive reader will likely be surprised by the "almost" from rule #3 in the previous section. Many other programming languages ensure object invariants through a combination of access control (making fields private so that all access and mutation happens only within a bounded set of methods) and concurrency control (to ensure only one thread can ever observe an object in an invalid state at one time). This ensures that objects are valid by default. Dafny instead approaches this by validating that any operation that requires an object to be valid (which in practice is nearly all of them) provides proof that this is true, based on the context of the operation. Thus Dafny objects are assumed invalid unless proven valid.

Because of this, disallowing all preconditions on external methods is extremely limiting: it means that absolutely nothing can be assumed about any Dafny objects in the control flow of external methods. It is often not possible to dynamically verify a predicate such as `Valid()` since it usually refers to ghost state, and even if it was possible would often be prohibitively expensive. It is also dangerous, however, to allow external methods to assume objects are in a `Valid()` state without proof, for the same reasons that we cannot allow stray `null` values to pollute the Dafny runtime.

If we assume and/or enforce certain invariants about the linkage between Dafny and external code, however, it is possible allow very specific pre- and post-conditions on external methods. Let's assume for the moment that Dafny objects can only be modified through Dafny methods, and not directly by external code referencing the internals of compiled code directly. This means if a predicate that reads some subset of the Dafny heap holds when control is passed to external code, it will remain true whenever Dafny code begins to execute again.

We can consider the implications while abusing Dafny notation. Since external code will be able to invoke exposed Dafny methods in any arbitrary order, the state of the Dafny heap after any one method must satisfy the requirements of all such methods. So:

```dafny
forall m: ExposedMethod, m': ExposedMethod :: m'.ensures() ==> m.requires()
```

Since native implementations will be able to turn around and invoke any externally-invokable method:

```dafny
forall m: ExposedMethod, n: NativeMethod :: n.requires() ==> m.requires()
```

If we make the simplifying assumption above that `ExposedMethod == NativeMethod` and label both as *external methods*, we have:

```dafny
forall m: ExternalMethod, m': ExternalMethod :: m'.requires() ==> m.requires() && m.ensures() ==> m.requires()
```

Therefore the pre-condition of every exposed method must be equivalent, and the post-condition of every such method must imply this pre-condition. We can refer to this single predicate as the *external invariant*. Although we may not know exactly what to make it, we at least know that the Dafny verifer should enforce that for every external method, its pre-condition must be equal to this invariant, and its post-condition at least as strong. That is:

```dafny
exists p: bool ::
  forall m: ExternMethod :: m.requires() == p && m.ensures() ==> p
```

### Defining the External Invariant

The question is now what to pick as the external invariant. Ideally this could be improved over time as Dafny's completeness improves over time.

Options:

* invariant = `true`, all objects immutable

* invariant = `forall v: Validatable :: v.Valid()`
  * Requires proving that if one object changes to another valid state, all other previously valid objects are still valid

* invariant = `forall v: Validatable :: v.Valid() && forall v': Validatable :: v != v' ==> v.Repr !! v'.Repr`


* Any object that doesn't implement Validatable must be strictly owned by an object that does. Assumption is that any such object either hasn't changed or is in the ValidatableRepr of another object in scope.
* Allow a subobject with a changing Repr iff you are the one making the change and can update your own Repr

### Other helpful Dafny features

1. **Discourage references to non-extern compiled elements**. The motivation here is to ensure external code does not interact with any part of the Dafny-generated code that has not been validated as safe to expose externally. This is critical to ensure the above assumption that the set of Dafny objects does not change outside of Dafny source code, and to ensure that external code cannot intentionally or accidentally call or implement methods that were not verified as safe for external use.
   
   Ideally, the compiler would attach access control to non-external elements so this is enforced by the target language compiler and/or runtime. This would prevent Dafny-generated code in one package from referencing Dafny-generated code in another, however, which is a long-term goal. Therefore, we should instead intentionally munge the identifiers generated for non-external elements to discourage external references. This will likely involve appending something like `__DAFNY_INTERNAL__` to these identifiers.

1. **Support traits extending other traits**. This seems to be necessary in practice, so that a trait such as `ExternalList` can in turn extend a generic trait like `Validatable`. Working around the lack of this feature is very difficult, since both types want to reference ghost state such as `Repr`.

2. **Support singleton objects**. This would allow statically-referencable state in Dafny programs. It has some of the same challenges around non-local invariants, and may enable a more useful external invariant by tracking the set of externally-referencable objects as a static variable.

## One-Way Doors

There are two major categories of one-way doors, corresponding to the two aspects that are the most difficult to modify: the public API of the ESDK implementations we release and the semantics of the Dafny language itself.

The key priority is to expose an initial C# API that will meet customer's needs without committing to patterns of use we do not want to support in the future. This will likely mean ensuring all non-trivial types are exposed as only interfaces, and using factory methods rather than constructors.

## Open Questions

* Can we enforce that traits are the ONLY way to specify exposed or native methods for simplicity? This would require singleton objects in other to implement exposed static methods, such as factory methods.
* Can we/should we change the rules around :extern by default in Dafny 3.0, or should we introduce new keywords/attributes?
* I've largely skipped over termination proofs here. We will have to accept some measure of unsoundness here since external code cannot be analyzed, but we also don't want to give up and use `decreases *` across the whole ESDK code base. Can we find a middle-ground that allows for partial termination proof of the Dafny code, possibly looking something like `decreases Repr, *`?

