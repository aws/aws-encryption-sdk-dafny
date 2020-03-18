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
        private ESDKClient.EncryptorStream stream;

        public EncryptionStream(ESDKClient.EncryptorStream stream) {
            this.stream = stream;
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
                Option<byte> readByteOpt = DafnyFFI.ExtractResult(stream.GetByte());
                // TODO generalize Option
                if (readByteOpt is Option_None<byte> none) {
                    // None means we've reached the end of the stream. no more to read.
                    break;
                } else if (readByteOpt is Option_Some<byte> some) {
                    byte readByte = some.get;
                    buffer[offset+n] = readByte;
                    n += 1;
                } else {
                    throw new ArgumentException(message: "Unrecognized STL.Option constructor");
                }
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
