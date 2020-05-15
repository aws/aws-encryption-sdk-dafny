using System;
using System.IO;
using ToyUTF8Transform;
using IO;
using STL;
using ibyteseq = Dafny.ISequence<byte>;

namespace AWSEncryptionSDK
{
    // UTF8TransformInStream maps a readable C# Stream to a Dafny BytesEnumerator
    // which wraps another readable C# Stream.
    public class UTF8TransformInStream : Stream {

        readonly private ToyEnumerator UTF8Transformer;
        readonly private Stream sourceStream;
        private MemoryStream outBuffer;
        // We ust maintain EOF state here if interface errors on read after EOF
        private bool atEOF;

        public UTF8TransformInStream(Stream sourceStream) {
            if (!sourceStream.CanRead) {
                throw new ArgumentException("Source stream supplied does not support reading");
            }
            this.sourceStream = sourceStream;

            // Set up the ToyEnumerator to work with the source stream
            // The way we do this is weird, using a C# constructor for the extern and the generated constructor
            // for the ToyEnumerator, but I'm not sure if we'll be able to avoid it
            var externWrapper = new ExternBytesEnumerator(sourceStream);
            var UTF8Transformer = new ToyEnumerator();
            UTF8Transformer.__ctor(externWrapper);

            this.UTF8Transformer = UTF8Transformer;
            this.outBuffer = new MemoryStream(); // TODO the way I use MemoryStream is hacky, update to use byte[] efficiently?
            this.atEOF = false;
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
            if (atEOF) {
                // 0 indicates EOF for C# read
                return 0;
            }
            
            // If outBuffer is empty, we should fill it
            if (outBuffer.Length - outBuffer.Position <= 0) {
                Option<ibyteseq> opt = DafnyFFI.ExtractResult(UTF8Transformer.Next());
                if (opt is Option_None<ibyteseq> none) {
                    atEOF = true;
                    return 0;
                } else if (opt is Option_Some<ibyteseq> bytes) {
                    // copy returned elements into the outBuffer
                    outBuffer = new MemoryStream(bytes.get.Elements);
                } else {
                    throw new ArgumentException(message: "Unrecognized STL.Option constructor");
                }
            }
            var readLen = outBuffer.Read(buffer, offset, count);
            return readLen;
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

        // This does not manage the sinkStream and the user MUST appropriately close it. i.e. we do not assume
        // that the sinkStream should close on this close.
        protected override void Dispose(bool disposing)
        {
            try {
                if (!atEOF) {
                    throw new Exception("UTF8TransformStream closed before UTF8Transformion finished.");
                }
            }
            finally {
                base.Dispose(disposing);
            }
        }

    }

    // UTF8TransformOutStream maps a readable C# Stream to a Dafny BytesEnumerator
    // which wraps another readable C# Stream.
    public class UTF8TransformOutStream : Stream {

        readonly private ToyAggregator UTF8Transformer;
        readonly private Stream sinkStream;

        public UTF8TransformOutStream(Stream sinkStream) {
            if (!sinkStream.CanWrite) {
                throw new ArgumentException("Source stream supplied does not support writing");
            }
            this.sinkStream = sinkStream;

            var externWrapper = new ExternBytesAggregator(sinkStream);
            var UTF8Transformer = new ToyAggregator();
            UTF8Transformer.__ctor(externWrapper);

            this.UTF8Transformer = UTF8Transformer;
        }

        public override bool CanRead
        {
            get
            {
                return false;
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
                return true;
            }
        }

        public override void Flush()
        {
          // MUST flush the underlying stream. This means that we must flush the underlying UTF8Transformer.
          // In our case, we need to indicate End, as having data buffered means that we require more
          // data in order to be valid. Without that data we are in a bad state. End() will appropraitely
          // return an error. Otherwise, this will signal end and flush the sink Stream.
          var _ = DafnyFFI.ExtractResult(UTF8Transformer.End());
          sinkStream.Flush();
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
            throw new NotSupportedException();
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
            var _ = DafnyFFI.ExtractResult(UTF8Transformer.Accept(DafnyFFI.SequenceFromByteArray(buffer, offset, count)));
        }
        
        // The sinkStream is NOT managed by this object,
        // and anyone using this Stream must appropriately close it
        protected override void Dispose(bool disposing)
        {
            try {
                // Release managed resources in UTF8Transformer by calling End().
                // In the ToyExample case, if there is anything in the buffer, we should error
                var _ = DafnyFFI.ExtractResult(UTF8Transformer.End());
            } finally {
                base.Dispose(disposing);
            }
        }
    }
}
