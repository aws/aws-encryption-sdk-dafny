namespace aws.polymorph


// Smithy doesn't allow passing resources or services as members of structures, 
// since it doesn't make sense in a client-server world to pass these over the
// wire. However, in our world we do want to be able to pass around references
// to things like Keyrings, so we create a new trait which indicates that 
// a target shape is not actually a structure but instead an opaque reference
// to a service or resource.
@trait(selector: "structure")
structure reference {
  // Can refer to either services or resources
  service: String,
  resource: String
}


// A trait for explicitly modeling the configuration options that should be
// available in the generated methods for creating clients.
@trait(selector: "service")
structure clientConfig {
    config: String
}

// A trait which indicates that the members of given structure should be
// expanded, to be used when we want operations to accept
// or return bare values rather than a nested structure.
// Code generation SHOULD throw an error if this is applied to a structure
// that is not used as input or output to an operation.
// Code generation MUST throw an error if this is applied to an output
// structures with more than one member.
// TODO: naming
@trait(selector: "structure")
structure positional {}

// Indicates that a string is represented as a sequence of UTF-8 encoded bytes
// in Dafny, rather than the default sequence of UTF-16 chars.
//
// This is a workaround that should be removed when Dafny's string definition
// is improved: <https://github.com/dafny-lang/dafny/issues/413>
@trait(selector: "string")
structure dafnyUtf8Bytes {}
