using System;
using System.IO;
using ESDKClient;
using STL;

namespace Collections {
    public partial class ExternByteProducer {
        // TODO should be readonly, however we can't set in constructor due to
        // weird extern-ness
        private Stream stream;

        public void SetInputStream(Stream stream) {
            this.stream = stream;
        }

        // TODO ideally this shouldn't be used
        // and instead we rely on a more efficient way
        // to read from the input stream
        public Result<byte> ExternNext() {
            byte[] bytes = new byte[1];
            stream.Read(bytes, 0, 1);
            return Result<byte>.create_Success(bytes[0]);
        }

        // TODO Need to assume that input stream is seekable.
        // If it is not, then we need to load everything into memory?
        // For now, just assume
        public bool ExternHasNext() {
            return stream.Position != stream.Length;
        }
        
        public int Length() {
            // TODO cutting off int sizes
            return (int)stream.Length;
        }
    }
}
