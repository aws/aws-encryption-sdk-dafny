module {:extern "Dafny.Aws"} Aws {
    // No content, this just creates the parent module so that
    // we can add sub-modules.

    // "Dafny" prefix on the extern because we are also generating
    // code in the "Aws.*" namespace from our Smithy-to-X code
    // generation and we need these to be separate
    // TODO: better name than "Dafny"?
}