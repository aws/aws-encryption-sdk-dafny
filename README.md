# AWS Encryption SDK Dafny

![Build Status - master branch](https://codebuild.us-west-2.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiVmIzeGwwQmY5bXdMQXg2aVBneWtDc3FHSWRHTjYrNnVUem9nNXJFUmY2Rk1yRnJvSjJvK3JCL2RScFRjSVF1UjA1elR3L0xpTVpiNmRZS0RyWjJpTnBFPSIsIml2UGFyYW1ldGVyU3BlYyI6InBBQm1tT1BPNjB3RU9XUS8iLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=master)

AWS Encryption SDK for Dafny

## License

This library is licensed under the Apache 2.0 License. 

## Building (the HKDF)

* You need to have a working Dafny installation and have Dafny.exe on your path
  * Dafny itself depends on Boogie and an SMT solver such as Z3.
* Download the BouncyCastle DLL by running e.g. `nuget install BouncyCastle` (requires `nuget` https://www.nuget.org/)
* Run `make hkdf` to verify and build the hkdf
* Run tests using `lit test` (requires the LLVM Integrated Tester `pip install lit`)