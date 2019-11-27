using System.Numerics;
using Xunit;

namespace EncryptionSDKTests
{
    public class ArraysTests
    {
        [Fact]
        public void CopyShouldWork()
        {
            var myArray = new int[] {1, 2, 3, 4, 5};
            var copy = Arrays.Array.copy(myArray, new BigInteger(5));
            Assert.Equal(myArray, copy);
        }
    }
}