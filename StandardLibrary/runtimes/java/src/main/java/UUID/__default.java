package UUID;

import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;

import java.nio.ByteBuffer;
import java.util.UUID;

import static software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence;
import static software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.dafny.conversion.ToNative.Simple.String;

public class __default  {

    public static Result<
            DafnySequence<? extends Byte>,
            DafnySequence<? extends Character>> ToByteArray(
                    final DafnySequence<? extends Character> s)
    {
        try {
            UUID fromString = UUID.fromString(String(s));
            ByteBuffer byteBuffer = ByteBuffer.wrap(new byte[16]);
            // In Java the UUID construction stores the 8 most significant bytes
            // and the 8 least significant bytes that add up to 16 byte UUID.
            byteBuffer.putLong(fromString.getMostSignificantBits());
            byteBuffer.putLong(fromString.getLeastSignificantBits());
            return Result.create_Success(
                    (DafnySequence<? extends Byte>) ByteSequence(byteBuffer)
            );
        } catch (Exception e) {
            return Result.create_Failure(
                    (DafnySequence<? extends Character>) CharacterSequence("Could not convert UUID to byte array.")
            );
        }
    }

    public static Result<
            DafnySequence<? extends Character>,
            DafnySequence<? extends Character>> FromByteArray(
            final DafnySequence<? extends Byte> b)
    {
        try {
            ByteBuffer byteBuffer = ByteBuffer.wrap((byte[]) Array.unwrap(b.toArray()));
            // In order to create a UUID in Java we need to supply
            // the most significant bytes and the least significant bytes
            // the construction calls for longs since it represents 8 bytes
            // 8 + 8 = 16 that make up the 16 bytes of the UUID construction.
            long high = byteBuffer.getLong();
            long low = byteBuffer.getLong();
            UUID fromByte = new UUID(high, low);
            return Result.create_Success(
                    (DafnySequence<? extends Character>) CharacterSequence(fromByte.toString())
            );
        } catch (Exception e) {
            return Result.create_Failure(
                    (DafnySequence<? extends Character>) CharacterSequence("Could not convert byte array to UUID.")
            );
        }

    }
    public static Result<
            DafnySequence<? extends Character>,
            DafnySequence<? extends Character>> GenerateUUID()
    {
        try {
            UUID uuid = UUID.randomUUID();
            return Result.create_Success(
                    (DafnySequence<? extends Character>) CharacterSequence(uuid.toString())
            );
        } catch (Exception e) {
            return Result.create_Failure(
                    (DafnySequence<? extends Character>) CharacterSequence("Could not generate a UUID.")
            );
        }

    }
}
