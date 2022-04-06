// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Text;
using Wrappers_Compile;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

// General-purpose utilities for invoking Dafny from C#,
// including converting between common Dafny and C# datatypes.
// Note this class is NOT intended to be part of the .NET ESDK API, but only
// for internal use in adapting between that API and the Dafny equivalent.
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

    public static T ExtractResult<T>(_IResult<T, icharseq> iResult)
    {
        Result<T, icharseq> result = (Result<T, icharseq>) iResult;
        if (result is Result_Success<T, icharseq> s) {
            return s.value;
        } else if (result is Result_Failure<T, icharseq> f) {
            // TODO-RS: Need to refine the wrapped value in a Failure so we
            // can throw specific exception types.
            throw new DafnyException(StringFromDafnyString(f.error));
        } else {
            throw new ArgumentException(message: "Unrecognized STL.Result constructor");
        }
    }

    public static _IOption<T> NullableToOption<T>(T t)
    {
        return t == null ? Option<T>.create_None() : Option<T>.create_Some(t);
    }

    public static _IResult<T, icharseq> CreateFailure<T>(string msg) where T : class
    {
        return Result<T, icharseq>.create_Failure(DafnyStringFromString(msg));
    }
}

public class DafnyException : Exception {
    public DafnyException(string message) : base(message) {
    }
}
