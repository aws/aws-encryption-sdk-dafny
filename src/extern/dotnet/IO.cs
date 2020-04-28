using System;
using System.IO;
using STL;

using ibyteseq = Dafny.ISequence<byte>;

namespace IO {
    public partial class ExternBytesEnumerator {
        readonly private Stream inputStream;

        readonly int MAX_READ_LEN = 4096; // arbitrary, currently what the Java ESDK uses

        public ExternBytesEnumerator(Stream inputStream) {
            this.inputStream = inputStream;
        }

        public Result<Option<ibyteseq>> NextExtern() {
            byte[] readBuffer = new byte[MAX_READ_LEN];
            int readLen;
            try {
                readLen = inputStream.Read(readBuffer, 0, readBuffer.Length);
            } catch (IOException e) {
                return Result<Option<ibyteseq>>.create_Failure(DafnyFFI.DafnyStringFromString(e.Message));
            } catch (ObjectDisposedException e) {
                return Result<Option<ibyteseq>>.create_Failure(DafnyFFI.DafnyStringFromString(e.Message));
            }
                
            if (readLen == 0) {
                return Result<Option<ibyteseq>>.create_Success(DafnyFFI.NullableToOption<ibyteseq>(null));
            }

            return Result<Option<ibyteseq>>.create_Success(DafnyFFI.NullableToOption(DafnyFFI.SequenceFromByteArray(readBuffer, 0, readLen)));
        }
    }

    public partial class ExternBytesAggregator {
        readonly private Stream outputStream;

        public ExternBytesAggregator(Stream outputStream) {
            this.outputStream = outputStream;
        }

        public Result<bool> AcceptExtern(ibyteseq element) {
            try {
                outputStream.Write(element.Elements, 0, element.Elements.Length);
                return Result<bool>.create_Success(true);
            } catch (IOException e) {
                return Result<bool>.create_Failure(DafnyFFI.DafnyStringFromString(e.Message));
            } catch (ObjectDisposedException e) {
                return Result<bool>.create_Failure(DafnyFFI.DafnyStringFromString(e.Message));
            }
        }

        public Result<bool> EndExtern() {
            // TODO Should this flush the sink stream, or should the caller be responsible for flushing it?
            // normally I'd say "yes", however things like CryptoStreams require you to FlushFinalFrame instead
            // of Flush. Given this implementation in the wild, I think it's reasonable to expect the user to do
            // this, as well as dispose the sink stream.
            return Result<bool>.create_Success(true);
        }
    } 
}
