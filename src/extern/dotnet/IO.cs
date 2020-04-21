using System;
using System.IO;
using STL;

using ibyteseq = Dafny.ISequence<byte>;

namespace IO {
    public partial class ExternBytesEnumerator {
        private Stream inputStream; //readonly?

        readonly int MAX_READ_LEN = 4096; // arbitrary, currently what the Java ESDK uses

        public ExternBytesEnumerator(Stream inputStream) {
            this.inputStream = inputStream;
        }

        public Result<Option<ibyteseq>> NextExtern() {
            byte[] readBuffer = new byte[MAX_READ_LEN];
            int readLen = inputStream.Read(readBuffer, 0, readBuffer.Length);
            if (readLen == 0) {
                // EOF
                return Result<Option<ibyteseq>>.create_Success(DafnyFFI.NullableToOption<ibyteseq>(null));
            }

            // Copy and trim read bytes into new sequence
            byte[] byteChunk = new byte[readLen];
            Array.Copy(readBuffer, 0, byteChunk, 0, readLen);
            // And then they get copied again :).
            return Result<Option<ibyteseq>>.create_Success(DafnyFFI.NullableToOption(DafnyFFI.SequenceFromByteArray(byteChunk)));
        }
    }
}
