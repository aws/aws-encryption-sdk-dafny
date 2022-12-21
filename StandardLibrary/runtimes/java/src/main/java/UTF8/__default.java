package UTF8;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CharsetEncoder;
import java.nio.charset.StandardCharsets;

import Wrappers_Compile.Result;
import dafny.DafnySequence;

import static software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence;
import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

// The only way to keep this thread/concurrent safe/ is
// to create a new Coder everytime.
// If we wanted to increase performance,
// we could declare this NOT thread/concurrent safe,
// and reset the coder everytime.
public class __default extends UTF8._ExternBase___default {

    // This is largely copied from Polymorph's dafny-java-conversion:
    // software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes
    public static Result<
            DafnySequence<? extends Byte>,
            DafnySequence<? extends Character>> Encode(
                    final DafnySequence<? extends Character> s) {
        Charset utf8 = StandardCharsets.UTF_8;
        // See thread/concurrent safe comment above class
        CharsetEncoder coder = utf8.newEncoder();
        CharBuffer inBuffer = CharBuffer.wrap(String(s));
        inBuffer.position(0);
        try {
            ByteBuffer outBuffer = coder.encode(inBuffer);
            // outBuffer's capacity can be much higher than the limit.
            // By taking just the limit, we ensure we do not include
            // any allocated but un-filled space.
            return Result.create_Success(
                    (DafnySequence<? extends Byte>) ByteSequence(outBuffer, 0, outBuffer.limit()));
        } catch (CharacterCodingException ex) {
            return Result.create_Failure(
                    (DafnySequence<? extends Character>) CharacterSequence("Could not encode input to Dafny Bytes."));
        }
    }

    // This is largely copied from Polymorph's dafny-java-conversion:
    // software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes
    public static Result<
            DafnySequence<? extends Character>,
            DafnySequence<? extends Character>> Decode(
                    final DafnySequence<? extends Byte> s) {
        Charset utf8 = StandardCharsets.UTF_8;
        // See thread/concurrent safe comment above class
        CharsetDecoder coder = utf8.newDecoder();
        ByteBuffer inBuffer = ByteBuffer(s);
        inBuffer.position(0);
        try {
            CharBuffer outBuffer = coder.decode(inBuffer);
            outBuffer.position(0);
            return Result.create_Success(
                    (DafnySequence<? extends Character>) CharacterSequence(outBuffer.toString()));
        } catch (CharacterCodingException ex) {
            return Result.create_Failure(
                    (DafnySequence<? extends Character>) CharacterSequence("Could not encode input to Dafny Bytes."));
        }
    }

}
