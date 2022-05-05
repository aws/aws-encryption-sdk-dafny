# AWSEncryptionSDKBenchmarks

This project contains benchmarks for the .NET Encryption SDK implementation.
We use the [BenchmarkDotNet](https://benchmarkdotnet.org/) framework.

## Usage

All commands are to be run from this directory.

For more information about CLI arguments, see <https://benchmarkdotnet.org/articles/guides/console-args.html>.

### Running benchmarks

Note the single quotes!

```bash
$ # All benchmarks
$ dotnet run -c Release -f netcoreapp3.1 -- -f '*'

$ # Just encryption
$ dotnet run -c Release -f netcoreapp3.1 -- -f '*Encrypt'

$ # Just RawAesKeyring decryption
$ dotnet run -c Release -f netcoreapp3.1 -- -f '*RawAes*Decrypt'

$ # Just 1B and 1KB plaintexts, and just 4KB-byte frames
$ BENCHMARK_PLAINTEXT_LENGTH_BYTES=1,1000 \
    BENCHMARK_FRAME_LENGTH_BYTES=4096 \
    dotnet run -c Release -f netcoreapp3.1 -- -f '*'
```

The benchmarks will run, and dump output to both the console
and to the `BenchmarkDotNet.Artifacts` directory.

### List available benchmarks

```bash
$ dotnet run -c Release -f netcoreapp3.1 -- --list flat
```

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
