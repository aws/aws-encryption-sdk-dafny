using System.Collections.Generic;
using System.Linq;
using icharseq = Dafny.ISequence<char>;

namespace AWSEncryptionSDK
{
    public class AWSKMSClientSuppliers {
        public static KMSUtils.BaseClientSupplier NewKMSDefaultClientSupplier()
        {
            // TODO awslabs/aws-encryption-sdk-dafny/issues/198: This will be swapped for the caching client supplier
            return NewKMSBaseClientSupplier();
        }

        public static KMSUtils.BaseClientSupplier NewKMSBaseClientSupplier()
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
            // instantiate the class and then manually call __ctor() to call the required constructor
            KMSUtils.BaseClientSupplier clientSupplier = new KMSUtils.BaseClientSupplier();
            clientSupplier.__ctor();
            return clientSupplier;
        }

        public static KMSUtils.LimitRegionsClientSupplier NewKMSLimitRegionsClientSupplier(KMSUtils.AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
            // instantiate the class and then manually call __ctor() to call the required constructor
            KMSUtils.LimitRegionsClientSupplier limitRegionsclientSupplier = new KMSUtils.LimitRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            limitRegionsclientSupplier.__ctor(clientSupplier, Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return limitRegionsclientSupplier;
        }

        public static KMSUtils.ExcludeRegionsClientSupplier NewKMSExcludeRegionsClientSupplier(KMSUtils.AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to
            // instantiate the class and then manually call __ctor() to call the required constructor
            KMSUtils.ExcludeRegionsClientSupplier excludeRegionsclientSupplier = new KMSUtils.ExcludeRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            excludeRegionsclientSupplier.__ctor(clientSupplier, Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return excludeRegionsclientSupplier;
        }
    }
}
