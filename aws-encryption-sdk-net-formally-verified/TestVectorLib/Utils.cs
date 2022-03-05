using System;
using System.IO;
using Newtonsoft.Json.Linq;

namespace TestVectors
{
    public static class Utils
    {
        public static string GetEnvironmentVariableOrError(string key) {
            string nullableResult = Environment.GetEnvironmentVariable(key);
            if (nullableResult == null) {
                throw new ArgumentException($"Environment Variable {key} must be set");
            }
            return nullableResult;
        }

        public static T LoadObjectFromPath<T>(string path)
        {
            if (!File.Exists(path)) {
                throw new ArgumentException($"File not found: {path}");
            }
            string contents = File.ReadAllText(path);
            JObject obj = JObject.Parse(contents);
            return obj.ToObject<T>();
        }

        public static string ManifestUriToPath(string uri, string manifestPath) {
            // Assumes files referenced in manifests starts with 'file://'
            if (!string.Equals(uri.Substring(0, 7), "file://")) {
                throw new ArgumentException($"Malformed filepath in manifest (needs to start with 'file://'): {uri}");
            }

            DirectoryInfo parentDir = Directory.GetParent(manifestPath);
            if (parentDir == null)
            {
                throw new ArgumentException($"Couldn't find parent directory of {manifestPath}");
            }

            return Path.Combine(parentDir.ToString(), uri.Substring(7));
        }
    }
}
