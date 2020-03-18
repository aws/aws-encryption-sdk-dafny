using System;
using System.IO;
using EncryptionStreams;
using STL;

namespace ESDKClientStreams {
    // This wraps a readable C# Stream around the Dafny EncryptionStream.
    // Right now this relies on Encryption Stream having a Next() method
    // in order to get the underlying 'Accept'-ed bytes.
    // TODO: Implement IDisposable interface
    public class ClientEncryptionStream : Stream {

        readonly private EncryptionStream encryptor;

        public ClientEncryptionStream(EncryptionStream encryptor) {
            this.encryptor = encryptor;
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
          // Do nothing. Docs say to do this instead of throw because
          // it should be valid to flush a readonly stream
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
            while (n < count) {
                // TODO This is byte by byte currently. EncryptionStream needs to enable
                // getting bytes in chunks.
                Option<byte> readByteOpt = DafnyFFI.ExtractResult(encryptor.GetByte());
                // TODO generalize Option check
                if (readByteOpt is Option_None<byte> none) {
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
