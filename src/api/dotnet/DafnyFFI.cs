using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using STL;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

// General-purpose utilities for invoking Dafny from C#,
// including converting between common Dafny and C# datatypes. 
public class DafnyFFI {

    public static byte[] ByteArrayFromSequence(ibyteseq seq) {
        // TODO: Find a way to safely avoid copying 
        byte[] copy = new byte[seq.Elements.Length];
        Array.Copy(seq.Elements, 0, copy, 0, seq.Elements.Length);
        return copy;
    }

    public static MemoryStream MemoryStreamFromSequence(ibyteseq seq) {
        return new MemoryStream(ByteArrayFromSequence(seq));
    }
  
    public static ibyteseq SequenceFromMemoryStream(MemoryStream bytes) {
        // TODO: Find a way to safely avoid copying 
        return SequenceFromByteArray(bytes.ToArray());
    }

    public static ibyteseq SequenceFromByteArray(byte[] bytearray) {
        return byteseq.FromArray(bytearray);
    }
  
    public static string StringFromDafnyString(icharseq dafnyString) {
        // TODO: Find a way to safely avoid copying.
        // The contents of a Dafny.Sequence should never change, but since a Dafny.ArraySequence
        // currently allows direct access to its array we can't assume that's true.
        return new string(dafnyString.Elements);
    }
    
    public static icharseq DafnyStringFromString(string s) {
        // This is safe since string#ToCharArray() creates a fresh array
        return charseq.FromArray(s.ToCharArray());
    }
    
    public static ibyteseq DafnyUTF8BytesFromString(string s) {
        return byteseq.FromArray(Encoding.UTF8.GetBytes(s));
    }
  
    public static T ExtractResult<T>(Result<T> result) {
        if (result is Result_Success<T> s) {
            return s.value;
        } else if (result is Result_Failure<T> f) {
            // TODO-RS: Need to refine the wrapped value in a Failure so we
            // can throw specific exception types.
            throw new DafnyException(StringFromDafnyString(f.error));
        } else {
            throw new ArgumentException(message: "Unrecognized STL.Result constructor");
        }
    }

    public static Option<T> NullableToOption<T>(T t)
    {
        return t == null ? Option<T>.create_None() : Option<T>.create_Some(t);
    }

    public enum RSAPaddingModes {
        PKCS1, OAEP_SHA1, OAEP_SHA256, OAEP_SHA384, OAEP_SHA512
    }

    public static RSAEncryption.PaddingMode RSAPaddingModesToDafnyPaddingMode(RSAPaddingModes paddingModes)
    {
        switch (paddingModes) {
            case RSAPaddingModes.PKCS1:
                return RSAEncryption.PaddingMode.create_PKCS1();
            case RSAPaddingModes.OAEP_SHA1:
                return RSAEncryption.PaddingMode.create_OAEP__SHA1();
            case RSAPaddingModes.OAEP_SHA256:
                return RSAEncryption.PaddingMode.create_OAEP__SHA256();
            case RSAPaddingModes.OAEP_SHA384:
                return RSAEncryption.PaddingMode.create_OAEP__SHA384();
            case RSAPaddingModes.OAEP_SHA512:
                return RSAEncryption.PaddingMode.create_OAEP__SHA512();
            default:
                throw new ArgumentException("Unsupported RSA Padding Mode");
        };
    }

    public enum AESWrappingAlgorithm {
        AES_GCM_128, AES_GCM_192, AES_GCM_256
    }

    public static string AESWrappingAlgorithmToGeneratorUtilitiesAlgorithm(AESWrappingAlgorithm wrappingAlgorithm)
    {
        switch (wrappingAlgorithm) {
            case AESWrappingAlgorithm.AES_GCM_128:
                return "AES128";
            case AESWrappingAlgorithm.AES_GCM_192:
                return "AES192";
            case AESWrappingAlgorithm.AES_GCM_256:
                return "AES256";
            default:
                throw new ArgumentException("Unsupported AES Wrapping Algorithm");
        };
    }

    public static EncryptionSuites.EncryptionSuite AESWrappingAlgorithmToDafnyWrappingAlgorithm(AESWrappingAlgorithm wrappingAlgorithm)
    {
        switch (wrappingAlgorithm) {
            case AESWrappingAlgorithm.AES_GCM_128:
                return EncryptionSuites.__default.AES__GCM__128;
            case AESWrappingAlgorithm.AES_GCM_192:
                return EncryptionSuites.__default.AES__GCM__192;
            case AESWrappingAlgorithm.AES_GCM_256:
                return EncryptionSuites.__default.AES__GCM__256;
            default:
                throw new ArgumentException("Unsupported AES Wrapping Algorithm");
        };
    }

    public static KMSUtils.BaseClientSupplier NewKMSDefaultClientSupplier()
    {
        // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
        // instantiate the class and then manually call __ctor() to call the required constructor
        // TODO awslabs/aws-encryption-sdk-dafny/issues/198: This will be swapped for the caching client supplier
        KMSUtils.BaseClientSupplier clientSupplier = new KMSUtils.BaseClientSupplier();
        clientSupplier.__ctor();
        return clientSupplier;
    }

    public static KMSUtils.BaseClientSupplier NewKMSBaseClientSupplier()
    {
        // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
        // instantiate the class and then manually call __ctor() to call the required constructor
        KMSUtils.BaseClientSupplier clientSupplier = new KMSUtils.BaseClientSupplier();
        clientSupplier.__ctor();
        return clientSupplier;
    }

    public static KMSUtils.LimitRegionsClientSupplier NewKMSLimitRegionsClientSupplier(KMSUtils.KMSClientSupplier clientSupplier, IEnumerable<string> regions)
    {
        // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
        // instantiate the class and then manually call __ctor() to call the required constructor
        KMSUtils.LimitRegionsClientSupplier limitRegionsclientSupplier = new KMSUtils.LimitRegionsClientSupplier();
        var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
        limitRegionsclientSupplier.__ctor(clientSupplier, Dafny.Sequence<icharseq>.FromElements(convertedRegions));
        return limitRegionsclientSupplier;
    }

    public static KMSUtils.ExcludeRegionsClientSupplier NewKMSExcludeRegionsClientSupplier(KMSUtils.KMSClientSupplier clientSupplier, IEnumerable<string> regions)
    {
        // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
        // instantiate the class and then manually call __ctor() to call the required constructor
        KMSUtils.ExcludeRegionsClientSupplier excludeRegionsclientSupplier = new KMSUtils.ExcludeRegionsClientSupplier();
        var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
        excludeRegionsclientSupplier.__ctor(clientSupplier, Dafny.Sequence<icharseq>.FromElements(convertedRegions));
        return excludeRegionsclientSupplier;
    }
}

public class DafnyException : Exception {
    public DafnyException(string message) : base(message) {
    }
}
