# AWS Encryption SDK Dafny

test2

![Build Status - master branch](https://codebuild.us-west-2.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiVmIzeGwwQmY5bXdMQXg2aVBneWtDc3FHSWRHTjYrNnVUem9nNXJFUmY2Rk1yRnJvSjJvK3JCL2RScFRjSVF1UjA1elR3L0xpTVpiNmRZS0RyWjJpTnBFPSIsIml2UGFyYW1ldGVyU3BlYyI6InBBQm1tT1BPNjB3RU9XUS8iLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=master)

AWS Encryption SDK for Dafny

## Building

To build, the AWS Encryption SDK requires the most up to date version of [dafny](https://github.com/dafny-lang/dafny) on your PATH.

Building and verifying also requires [nuget](https://www.nuget.org/) to retrieve some dependencies.

To build all files into one main executable:

```
make build
```

To run the dafny verifier across all files:

```
make verify
```

## Testing

Requires install of the [LLVM Integrated Tester](https://llvm.org/docs/CommandGuide/lit.html (available through `pip install lit`).

Run the test suite with:

```
make test
```

## License

This library is licensed under the Apache 2.0 License.
