// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Newtonsoft.Json;
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

        /// <summary>
        /// Serializes the given object as JSON and writes it to the given path.
        /// Throws if the file already exists.
        /// <para>
        /// Note that NO exception will be thrown if the object has a null value on a required property.
        /// </para>
        /// </summary>
        public static void WriteObjectToPath<T>(T obj, string path)
        {
            // Do this first in order to avoid serializing if opening the file fails anyway
            using var fs = new FileStream(path, FileMode.CreateNew);

            using var stringWriter = new StringWriter();
            var serializer = new JsonSerializer
            {
                Formatting = Formatting.Indented,
                // WARNING: We set this option in order to omit null optional values.
                // But it "overrides" the `JsonRequired` behavior on serialization -
                // if the object has a null required value,
                // the serializer will just ignore it without throwing an exception.
                NullValueHandling = NullValueHandling.Ignore,
            };
            serializer.Serialize(stringWriter, obj);
            fs.Write(Encoding.UTF8.GetBytes(stringWriter.ToString()));
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

        /// <summary>
        /// Writes the data of each name-data pair into a new, correspondingly-named file.
        /// Throws if any file already exists.
        /// </summary>
        /// <param name="dir">the directory in which to create new files</param>
        /// <param name="namedData">the collection of name-data pairs</param>
        public static void WriteNamedDataMap(DirectoryInfo dir, Dictionary<string, MemoryStream> namedData)
        {
            foreach (var (name, data) in namedData)
            {
                WriteBinaryFile(dir, name, data);
            }
        }

        /// <summary>
        /// Writes the given data into a new file.
        /// Throws if the file already exists.
        /// </summary>
        /// <param name="dir">the directory in which to create the new file</param>
        /// <param name="name">the name of the file</param>
        /// <param name="data">the data to be written</param>
        public static void WriteBinaryFile(DirectoryInfo dir, string name, MemoryStream data)
        {
            var path = Path.Join(dir.FullName, name);
            using var fs = new FileStream(path, FileMode.CreateNew);
            using var writer = new BinaryWriter(fs);
            writer.Write(data.ToArray());
        }
    }
}
