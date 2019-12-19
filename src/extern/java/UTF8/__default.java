package UTF8;

import dafny.DafnySequence;
import dafny.UByte;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.*;

public class __default extends _ExternBase___default {
    public static STL.Result<DafnySequence<UByte>> Encode(DafnySequence<Character> str) {
        CharsetEncoder utf8 = StandardCharsets.UTF_8.newEncoder();
        utf8.onMalformedInput(CodingErrorAction.REPORT);
        utf8.onUnmappableCharacter(CodingErrorAction.REPORT);
        try {
            ByteBuffer utf8Buf = utf8.encode(CharBuffer.wrap(str.verbatimString()));
            byte[] utf8Bytes = new byte[utf8Buf.limit()];
            utf8Buf.get(utf8Bytes);
            return new STL.Result_Success<>(DafnySequence.fromBytesUnsigned(utf8Bytes));
        } catch (CharacterCodingException e) {
            return new STL.Result_Failure<>(DafnySequence.asString("Input contains invalid Unicode characters"));
        }
    }

    public static STL.Result<DafnySequence<Character>> Decode(DafnySequence<UByte> bytes) {
        CharsetDecoder utf8 = StandardCharsets.UTF_8.newDecoder();
        utf8.onMalformedInput(CodingErrorAction.REPORT);
        utf8.onUnmappableCharacter(CodingErrorAction.REPORT);
        try {
            String decoded = utf8.decode(ByteBuffer.wrap(DafnySequence.toByteArrayUnsigned(bytes))).toString();
            return new STL.Result_Success<>(DafnySequence.asString(decoded));
        } catch (CharacterCodingException e) {
            return new STL.Result_Failure<>(DafnySequence.asString("Input contains an invalid Unicode code point"));
        }
    }
}
