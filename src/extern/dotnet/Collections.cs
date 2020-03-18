using System;
using System.IO;
using ESDKClient;
using STL;

namespace Collections {
    public partial class InputStreamByteProducer {
        // TODO should be readonly, however we can't set in constructor due to
        // weird extern-ness
        private Stream inputStream;

        public InputStreamByteProducer(Stream inputStream) {
            this.inputStream = inputStream;
        }

        // TODO ideally this shouldn't be used
        // and instead we rely on a more efficient way
        // to read from the input stream.
        // i.e. There should be a Siphon that is able
        // to make use of a more efficient read for C# read
        public Result<byte> ExternNext() {
            byte[] bytes = new byte[1];
            inputStream.Read(bytes, 0, 1);
            return Result<byte>.create_Success(bytes[0]);
        }

        // TODO Assumes that the input stream is seekable.
        public bool ExternHasNext() {
            return inputStream.Position != inputStream.Length;
        }
        
        // TODO Assumes that the input stream is seekable.
        // Ideally, we shouldn't need the ByteProducer to expose this.
        public int Length() {
            // TODO cutting off long sizes
            return (int)inputStream.Length;
        }
    }
}
