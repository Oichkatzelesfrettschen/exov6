#!/usr/bin/env node
// @file file_count.js
// @brief Count files in the repository using Node.js and glob.
import { glob } from 'glob';

async function countFiles() {
  const files = await glob('**/*', { nodir: true, dot: true });
  console.log(`Node glob count: ${files.length}`);
}

countFiles();
