# AWSEncryptionSDKBenchmarks

This project contains benchmarks for the .NET Encryption SDK implementation.
We use the [BenchmarkDotNet](https://benchmarkdotnet.org/) framework.

## Usage

All commands to be run from this directory.

Run all benchmarks (note the single quotes!):

```bash
$ dotnet run -c Release -- -f '*'
```

List available benchmarks:

```bash
$ dotnet run -c Release -- --list flat
```

Run particular benchmarks:

```
$ # just the encryption benchmarks
$ dotnet run -c Release -- -f '*Encrypt'

$ # just the decryption benchmarks
$ dotnet run -c Release -- -f '*Decrypt'
```

The benchmarks will run, and dump output to both the console
and to the `BenchmarkDotNet.Artifacts` directory.

## Troubleshooting

### Failed to set up high priority

BenchmarkDotNet spins up new processes for running separate benchmarks,
and so it needs to manipulate the CPU priority of those processes.
If it's unable to do so, you may see some console output that says

> Failed to set up high priority

You can work around this by running the benchmark suite as superuser, e.g.

```bash
$ sudo dotnet run -c Release
```
