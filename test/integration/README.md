This directory holds dafny and C# code which decrypts the kms test vectors in https://github.com/awslabs/aws-crypto-tools-test-vector-framework

To run the tests, download and unzip a set of vectors in this directory.
Then run the following commands:

```
dafny TestVectorModels.dfy TestVectorExterns.cs ../../src/extern/dotnet/UTF8.cs ../../src/extern/dotnet/Random.cs ../../src/extern/dotnet/AESEncryption.cs BouncyCastle.Crypto.dll  ../../src/extern/dotnet/Signature.cs ../../src/extern/dotnet/HKDF-extern.cs ../../src/extern/dotnet/Arrays-extern.cs ../../src/extern/dotnet/RSAEncryption.cs ../../src/extern/dotnet/KMS.cs AWSSDK.Core.dll AWSSDK.KeyManagementService.dll Newtonsoft.Json.dll /noVerify /compile:2
mono TestVectorModels.exe
```

Note that this is NOT how this should be built in the future.
All dependent .dll files are included here for convenience sake, but in the future should be managed by a proper build system.
