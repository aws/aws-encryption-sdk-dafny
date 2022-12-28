# DDB Model

This AWS-DDB module is a work in progress, and currently requires some updates in order to successfully build a model and corresponding types with Polymorph. [See README-ERATA.md](./README-ERATA.md).

### Development Requirements

See dependencies used by CI workflow.
TODO: Better define and maintain (via CI) dev dependencies for this module

### Build

#### Transpile Dafny into .NET

```
make transpile_net
```

Transpiles the dafny code into .NET.

#### Build Java

```
make build_java
```

Transpiles the dafny code in Java, then builds all Java.
Also builds and locally deploys all dependencies.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
