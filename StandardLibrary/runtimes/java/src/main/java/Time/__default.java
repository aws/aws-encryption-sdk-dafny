package Time;

import Wrappers_Compile.Result;
import dafny.DafnySequence;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.TimeZone;

public class __default {
    public static Long CurrentRelativeTime() {
        return System.currentTimeMillis() / 1000;
    }

    public static Result<DafnySequence<? extends Character>, DafnySequence<? extends Character>> GetCurrentTimeStamp() {
        try {
            TimeZone tz = TimeZone.getTimeZone("UTC");
            DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss:SSSSSS'Z'"); // Quoted "Z" to indicate UTC, no timezone offset
            df.setTimeZone(tz);
            return  Result.create_Success(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(df.format(new Date())));
        } catch (Exception var1) {
            return Result.create_Failure(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence("Could not generate a timestamp in ISO8601."));
        }
    }
}
