using System;
using System.IO;
using ESDKClient;
using STL;

// TODO I can't name this EncryptionStream :'(
namespace EncryptionStreams {
    // What's used internally and exposes externally should be different... Right now the C# interface
    // is used for both
    // TODO implement Disposable, wrap stream in friendly handlers
    public partial class EncryptionStream : Stream {
        // TODO what should the underlying stream actually be?
        // TODO should be readonly
        private ESDKClient.EncryptTheRestStream encryptorStream;
        private ESDKClient.EncryptInputStream inputStream;

        public EncryptionStream(ESDKClient.EncryptInputStream inputStream, ESDKClient.EncryptTheRestStream encryptorStream) {
            this.inputStream = inputStream;
            this.encryptorStream = encryptorStream;
        }

        public override bool CanRead
        {
            get
            {
                return true;
            }
        }

        public override bool CanSeek
        {
            get
            {
                return false;
            }
        }

        public override bool CanWrite
        {
            get
            {
                return false;
            }
        }

        public override void Flush()
        {
          // Do nothing. Docs say to do this instead of throw because it should be valid to flush a readonly stream
        }

        public override long Length
        {
            get
            {
                throw new NotSupportedException();
            }
        }

        public override long Position
        {
            get
            {
                throw new NotSupportedException();
            }
            set
            {
                throw new NotSupportedException();
            }
        }

        public override int Read(byte[] buffer, int offset, int count)
        {
            int n = 0;
            // FIXME currently initializing buffer fo revery read. obvi fix this
            // also naming collision

            // Need to abstract more so that we do not have to byte by byte HasNext()
            while (n < count) {
                while (!encryptorStream.HasNext()) {
                    // TODO annoying BigInteger >:(
                    System.Numerics.BigInteger siphoned = DafnyFFI.ExtractResult(inputStream.Siphon(encryptorStream));
                    // there is no more to siphon. End of composite stream.
                    if (siphoned == 0) {
                        return n;
                    }
                    // assert HasNext()?
                }
                byte readByte = DafnyFFI.ExtractResult(encryptorStream.Next());

                // TODO 0 could be a failure or EOF, which is unfortunate.
                // For now just read it as is. Implement proper failures later.
                buffer[offset+n] = readByte;
                n += 1;
            }
            return n;
        }

        public override long Seek(long offset, SeekOrigin origin)
        {
            throw new NotSupportedException();
        }

        public override void SetLength(long value)
        {
            throw new NotSupportedException();
        }

        public override void Write(byte[] buffer, int offset, int count)
        {
            throw new NotSupportedException();
        }
    }
}
