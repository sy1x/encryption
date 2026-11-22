import { execFile, spawn } from 'node:child_process'
import {
  createCipheriv, createDecipheriv, createHash, createHmac, hkdfSync,
  randomBytes, randomInt, scrypt, timingSafeEqual,
} from 'node:crypto'
import { constants } from 'node:fs'
import {
  link, lstat, mkdir, mkdtemp, open, readFile, readdir, realpath, rename, rm, rmdir, unlink,
} from 'node:fs/promises'
import { homedir, hostname, release } from 'node:os'
import { basename, dirname, isAbsolute, join, relative } from 'node:path'
import { createInterface } from 'node:readline/promises'
import { Writable } from 'node:stream'
import { fileURLToPath } from 'node:url'
import { promisify } from 'node:util'

const project = dirname(fileURLToPath(import.meta.url))
const vault = join(project, '.vault')
const files = join(vault, 'files')
const checkouts = join(vault, 'checkout')
const identityPath = join(vault, 'identity.json')
const optionsPath = join(vault, 'options.json')
const sessionLock = join(project, '.vault-session')
const resetPath = join(project, '.vault-reset')
const projectFiles = new Set(['vault.sh', 'vault.mjs', 'eff_large_wordlist.txt', 'README.md', '.gitignore'])
const stop = new AbortController()
const derivePassword = promisify(scrypt)
const legacyMagic = Buffer.from('LVLT0001')
const magic = Buffer.from('LVLT0002')
const headerSize = magic.length + 32 + 12 + 12 + 2
const tagSize = 16
const maxBytes = 2 ** 36 - 32 // Maximum plaintext for a single AES-GCM message.
const readFlags = constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK
const color = process.stdout.isTTY && process.env.TERM !== 'dumb' && !('NO_COLOR' in process.env)

function print(message = '') {
  console.log(message)
}

function display(value) {
  return JSON.stringify(value).replace(/[\u007f-\u009f\u202a-\u202e\u2066-\u2069]/gu,
    character => '\\u' + character.charCodeAt(0).toString(16).padStart(4, '0'))
}

function panel(title) {
  if (process.stdout.isTTY && process.env.TERM !== 'dumb') {
    process.stdout.write('\x1b[2J\x1b[H')
  }
  const line = '+--------------------------------------------+'
  const banner = line + '\n| ' + title.padEnd(42) + ' |\n' + line
  print(color ? '\x1b[1;36m' + banner + '\x1b[0m' : banner)
}

function within(parent, path) {
  const part = relative(parent, path)
  return part !== '..' && !part.startsWith('../') && !isAbsolute(part)
}

async function ensurePrivateDirectory(path) {
  try {
    await mkdir(path, { mode: 0o700 })
  } catch (error) {
    if (error.code !== 'EEXIST') throw error
    const info = await lstat(path)
    if (!info.isDirectory() || info.uid !== process.getuid() || (info.mode & 0o077)) {
      throw new Error('Expected a private directory owned by you at ' + display(path))
    }
  }
}

async function syncDirectory(path) {
  const handle = await open(path, constants.O_RDONLY | constants.O_DIRECTORY)
  try {
    await handle.sync()
  } finally {
    await handle.close()
  }
}

async function acquireSession() {
  try {
    await mkdir(sessionLock, { mode: 0o700 })
  } catch (error) {
    if (error.code !== 'EEXIST') throw error
    throw new Error('The vault is locked by another session. See README.md if the previous session crashed.')
  }
}

async function finishReset() {
  let info
  try {
    info = await lstat(resetPath)
  } catch (error) {
    if (error.code === 'ENOENT') return
    throw error
  }
  if (!info.isDirectory() || info.uid !== process.getuid() || (info.mode & 0o077)) {
    throw new Error('Expected a private reset directory owned by you at ' + display(resetPath))
  }
  await syncDirectory(project)
  await rm(resetPath, { recursive: true, force: true })
  await syncDirectory(project)
}

async function resetVault(ask) {
  panel('LOCAL VAULT / RESET')
  print('  Reset permanently deletes all files stored in this vault, its settings,')
  print('  and its decryption identity. A new vault cannot decrypt any old files.')
  print('  Plaintext checked out elsewhere and external backups may still exist.')
  if (await ask('Type RESET to erase this vault (Enter cancels)> ') !== 'RESET') {
    print('Reset canceled.')
    return false
  }
  stop.signal.throwIfAborted()
  await rename(vault, resetPath)
  await finishReset()
  print('Vault erased. Set up a new credential.')
  return true
}

async function prepareVault() {
  await ensurePrivateDirectory(vault)
  await ensurePrivateDirectory(files)
  await ensurePrivateDirectory(checkouts)
  // Persist the new directory entries before the first import can remove anything.
  await syncDirectory(project)
  await syncDirectory(vault)
}

async function readPrivateJSON(path) {
  let handle
  try {
    handle = await open(path, readFlags)
  } catch (error) {
    if (error.code === 'ENOENT') return null
    throw error
  }
  try {
    const info = await handle.stat()
    if (!info.isFile() || info.uid !== process.getuid() || (info.mode & 0o077) || info.size > 4096) {
      throw new Error('Expected a private configuration file at ' + display(path))
    }
    const data = JSON.parse(await handle.readFile('utf8'))
    if (!data || typeof data !== 'object' || Array.isArray(data)) {
      throw new Error('Invalid configuration at ' + display(path))
    }
    return data
  } finally {
    await handle.close()
  }
}

async function savePrivateJSON(path, data, replace = false) {
  const temporary = join(vault, '.config-' + randomBytes(16).toString('hex'))
  const handle = await open(temporary, 'wx', 0o600)
  try {
    try {
      await handle.writeFile(JSON.stringify(data, null, 2) + '\n')
      await handle.sync()
    } finally {
      await handle.close()
    }
    if (replace) await rename(temporary, path)
    else await link(temporary, path)
    await syncDirectory(vault)
  } finally {
    await rm(temporary, { force: true })
  }
}

function localTimestamp() {
  const now = new Date()
  const offset = -now.getTimezoneOffset()
  const time = new Date(now.getTime() + offset * 60_000).toISOString().slice(0, 19)
  const hours = String(Math.floor(Math.abs(offset) / 60)).padStart(2, '0')
  const minutes = String(Math.abs(offset) % 60).padStart(2, '0')
  return time + (offset < 0 ? '-' : '+') + hours + ':' + minutes
}

function hexKey(value) {
  return typeof value === 'string' && /^[a-f0-9]{64}$/u.test(value)
}

function validateIdentity(identity) {
  if (identity.version !== 1 || !['password', 'words'].includes(identity.mode)
      || !hexKey(identity.salt) || !hexKey(identity.localSecret) || !hexKey(identity.verifier)
      || typeof identity.created !== 'string'
      || !/^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d[+-]\d\d:\d\d$/u.test(identity.created)
      || typeof identity.number !== 'string' || !/^[1-9]\d{10}$/u.test(identity.number)) {
    throw new Error('Vault identity is invalid. Restore your original identity.json.')
  }
}

async function rootKey(password, identity) {
  const passwordKey = await derivePassword(password, Buffer.from(identity.salt, 'hex'), 32, {
    N: 2 ** 17, r: 8, p: 1, maxmem: 192 * 1024 * 1024,
  })
  try {
    const info = 'Local Vault v1 root\n' + identity.created + '\n' + identity.number
    return Buffer.from(hkdfSync('sha256', passwordKey, Buffer.from(identity.localSecret, 'hex'), info, 32))
  } finally {
    passwordKey.fill(0)
  }
}

function verifier(key) {
  return createHmac('sha256', key).update('Local Vault v1 unlock').digest()
}

function normalizeWords(words) {
  return words.trim().replace(/\s+/gu, ' ')
}

async function generateWords() {
  const data = await readFile(join(project, 'eff_large_wordlist.txt'))
  const checksum = createHash('sha256').update(data).digest('hex')
  if (checksum !== 'addd35536511597a02fa0a9ff1e5284677b8883b83e986e43f15a3db996b903e') {
    throw new Error('The bundled EFF word list is damaged. Restore eff_large_wordlist.txt.')
  }
  const words = data.toString('utf8').trim().split(/\r?\n/u)
    .map(line => line.split('\t')[1]).filter(word => /^[a-z]+$/u.test(word))
  const choices = words.length ** 2
  const limit = Math.floor(2 ** 32 / choices) * choices
  const context = JSON.stringify({
    purpose: 'Local Vault random word pairs v1',
    unixMilliseconds: Date.now(),
    monotonicNanoseconds: process.hrtime.bigint().toString(),
    hostname: hostname(),
    platform: process.platform,
    architecture: process.arch,
    release: release(),
    processId: process.pid,
    userId: process.getuid(),
    timezone: Intl.DateTimeFormat().resolvedOptions().timeZone,
  })
  // Time and environment provide context. The fresh OS seed supplies unpredictability.
  const seed = randomBytes(32)
  let counter = 0
  try {
    return Array.from({ length: 5 }, () => {
      let candidate
      do {
        const block = createHmac('sha256', seed).update(context).update(String(counter++)).digest()
        candidate = block.readUInt32BE(0)
      } while (candidate >= limit)
      // Rejection sampling keeps all word pairs equally likely.
      const index = candidate % choices
      return words[Math.floor(index / words.length)] + '-' + words[index % words.length]
    }).join(' ')
  } finally {
    seed.fill(0)
  }
}

async function initialize(ask) {
  if ((await readdir(files)).some(name => name.endsWith('.lvlt'))) {
    throw new Error('Vault identity is missing. Restore identity.json to recover files or run ./vault.sh --reset to erase them.')
  }
  panel('LOCAL VAULT / SETUP')
  print('  [1] Traditional password')
  print('  [2] Choose your own five words')
  print('  [3] Generate five random word pairs')
  const choice = (await ask('Choose 1, 2, or 3 (Enter cancels)> ')).trim()
  if (choice === '') return null
  if (!['1', '2', '3'].includes(choice)) throw new Error('Choose 1, 2, or 3 to initialize the vault.')
  const mode = choice === '1' ? 'password' : 'words'
  let password
  if (mode === 'words') {
    if (choice === '3') {
      password = await generateWords()
      panel('LOCAL VAULT / GENERATED WORDS')
      print('  Record all five word pairs in order, including the hyphens.')
      password.split(' ').forEach(word => print('  ' + word))
      await ask('Press Enter when recorded to hide the phrase> ')
    } else {
      let message = ''
      for (;;) {
        panel('LOCAL VAULT / FIVE WORDS')
        if (message) print(message)
        password = normalizeWords(await ask('Enter five words separated by spaces (Enter cancels)> ', true))
        if (!password) return null
        if (password.split(' ').length === 5) break
        message = 'Enter exactly five words.'
      }
    }
    panel('LOCAL VAULT / CONFIRM WORDS')
    const confirmation = normalizeWords(await ask('Re-enter the five words (Enter cancels)> ', true))
    if (!confirmation) return null
    if (confirmation !== password) throw new Error('The five words did not match. Setup was canceled.')
  } else {
    panel('LOCAL VAULT / PASSWORD')
    password = await ask('New password (Enter cancels)> ', true)
    if (password === '') return null
    panel('LOCAL VAULT / CONFIRM PASSWORD')
    if (password !== await ask('Confirm password> ', true)) throw new Error('The passwords did not match.')
  }
  const identity = {
    version: 1,
    mode,
    salt: randomBytes(32).toString('hex'),
    created: localTimestamp(),
    number: String(randomInt(10_000_000_000, 100_000_000_000)),
    localSecret: randomBytes(32).toString('hex'),
  }
  const key = await rootKey(password, identity)
  try {
    stop.signal.throwIfAborted()
    identity.verifier = verifier(key).toString('hex')
    await savePrivateJSON(identityPath, identity)
    print('Vault initialized. Keep a private backup of .vault/identity.json and your encrypted files.')
    return key
  } catch (error) {
    key.fill(0)
    throw error
  }
}

async function unlock(ask, identity) {
  validateIdentity(identity)
  const label = identity.mode === 'words' ? 'Five words' : 'Password'
  let message = ''
  for (;;) {
    panel('LOCAL VAULT / UNLOCK')
    if (message) print(message)
    let password = await ask(label + ' (Enter cancels)> ', true)
    if (password === '') return null
    if (identity.mode === 'words') password = normalizeWords(password)
    const key = await rootKey(password, identity)
    if (timingSafeEqual(verifier(key), Buffer.from(identity.verifier, 'hex'))) {
      return key
    }
    key.fill(0)
    message = 'Incorrect ' + label.toLowerCase() + '.'
  }
}

function fileKey(key, salt, purpose) {
  return Buffer.from(hkdfSync('sha256', key, salt, 'Local Vault v1 ' + purpose, 32))
}

function cipherFor(key, salt, purpose, nonce, aad, decrypt = false) {
  const derived = fileKey(key, salt, purpose)
  try {
    const create = decrypt ? createDecipheriv : createCipheriv
    const cipher = create('aes-256-gcm', derived, nonce, { authTagLength: tagSize })
    cipher.setAAD(aad)
    return cipher
  } finally {
    derived.fill(0)
  }
}

async function readExactly(handle, length, position) {
  const buffer = Buffer.alloc(length)
  for (let offset = 0; offset < length;) {
    const { bytesRead } = await handle.read(buffer, offset, length - offset, position + offset)
    if (!bytesRead) throw new Error('Unexpected end of file.')
    offset += bytesRead
  }
  return buffer
}

async function writeAll(handle, buffer) {
  for (let offset = 0; offset < buffer.length;) {
    const { bytesWritten } = await handle.write(buffer, offset, buffer.length - offset)
    if (!bytesWritten) throw new Error('Incomplete write.')
    offset += bytesWritten
  }
}

async function* chunks(handle, start, length) {
  const end = start + length
  for (let position = start; position < end;) {
    stop.signal.throwIfAborted()
    const chunk = await readExactly(handle, Math.min(1024 * 1024, end - position), position)
    yield chunk
    position += chunk.length
  }
}

function authenticatedEnd(decipher) {
  try {
    return decipher.final()
  } catch {
    throw new Error('Authentication failed. The file is damaged or belongs to a different vault.')
  }
}

async function writeEncrypted(input, output, size, pathBytes, key, salt) {
  const header = Buffer.concat([magic, salt, randomBytes(12), randomBytes(12), Buffer.alloc(2)])
  header.writeUInt16BE(pathBytes.length, headerSize - 2)
  const pathCipher = cipherFor(key, salt, 'path', header.subarray(40, 52), header)
  const metadata = Buffer.concat([pathCipher.update(pathBytes), pathCipher.final(), pathCipher.getAuthTag()])
  const prefix = Buffer.concat([header, metadata])
  await writeAll(output, prefix)

  const cipher = cipherFor(key, salt, 'contents', header.subarray(52, 64), prefix)
  const hash = createHash('sha256')
  for await (const chunk of chunks(input, 0, size)) {
    hash.update(chunk)
    await writeAll(output, cipher.update(chunk))
  }
  await writeAll(output, cipher.final())
  await writeAll(output, cipher.getAuthTag())
  return hash.digest()
}

async function readHeader(input, key) {
  const info = await input.stat()
  if (!info.isFile()) throw new Error('Expected a regular encrypted file.')
  const header = await readExactly(input, headerSize, 0)
  const length = header.readUInt16BE(headerSize - 2)
  const dataStart = headerSize + length + tagSize
  const size = info.size - dataStart - tagSize
  const version = header.subarray(0, magic.length)
  const legacy = version.equals(legacyMagic)
  if ((!legacy && !version.equals(magic)) || length < 1 || (legacy && length > 1024)
      || size < 0 || size > maxBytes) {
    throw new Error('Invalid or unsupported encrypted file.')
  }
  const metadata = await readExactly(input, length + tagSize, headerSize)
  const salt = header.subarray(8, 40)
  const decipher = cipherFor(key, salt, legacy ? 'filename' : 'path', header.subarray(40, 52), header, true)
  decipher.setAuthTag(metadata.subarray(length))
  const plain = Buffer.concat([decipher.update(metadata.subarray(0, length)), authenticatedEnd(decipher)])
  const location = plain.toString('utf8')
  const name = legacy ? location : basename(location)
  if (!Buffer.from(location, 'utf8').equals(plain) || location.includes('\0') || !name
      || name === '.' || name === '..' || name.includes('/')
      || (!legacy && (!isAbsolute(location) || location !== join(dirname(location), name)))) {
    throw new Error('Invalid stored file location.')
  }
  return {
    name, originalPath: legacy ? null : location, salt, dataStart, size, nonce: header.subarray(52, 64),
    prefix: Buffer.concat([header, metadata]),
  }
}

async function readContents(input, record, key, output) {
  const { salt, nonce, prefix, dataStart, size } = record
  const decipher = cipherFor(key, salt, 'contents', nonce, prefix, true)
  decipher.setAuthTag(await readExactly(input, tagSize, dataStart + size))
  const hash = createHash('sha256')
  for await (const chunk of chunks(input, dataStart, size)) {
    const plain = decipher.update(chunk)
    hash.update(plain)
    if (output) await writeAll(output, plain)
  }
  const tail = authenticatedEnd(decipher)
  hash.update(tail)
  if (output) await writeAll(output, tail)
  return hash.digest()
}

function sameSource(before, after) {
  return ['dev', 'ino', 'size', 'nlink', 'mtimeNs', 'ctimeNs'].every(field => before[field] === after[field])
}

function isProtected(path) {
  return (within(vault, path) && !within(checkouts, path))
    || within(resetPath, path) || within(sessionLock, path)
    || within(join(project, '.git'), path)
    || (dirname(path) === project && projectFiles.has(basename(path)))
}

async function importFile(path, key) {
  const leaf = basename(path)
  if (!leaf || path.endsWith('/') || leaf === '.' || leaf === '..') {
    throw new Error('Choose a regular file.')
  }
  // Resolve the parent before joining the leaf so symlink/.. follows filesystem semantics.
  const candidate = join(await realpath(dirname(path)), leaf)
  const preliminary = await lstat(candidate, { bigint: true })
  if (!preliminary.isFile() || preliminary.nlink !== 1n) {
    throw new Error('Choose a regular file with one filesystem link.')
  }
  const source = await realpath(candidate)
  const name = basename(source)
  if (isProtected(source)) {
    throw new Error('Choose a file outside the vault internals and project code.')
  }
  const input = await open(candidate, readFlags)
  try {
    const before = await input.stat({ bigint: true })
    if (!sameSource(preliminary, before)) throw new Error('The source changed before encryption.')
    const pathBytes = Buffer.from(source, 'utf8')
    if (before.size > BigInt(maxBytes) || pathBytes.length > 0xffff) {
      throw new Error('The file or its path exceeds the vault format limit.')
    }

    const salt = randomBytes(32)
    const id = salt.toString('hex')
    const destination = join(files, id + '.lvlt')
    const temporary = join(files, '.import-' + id)
    const output = await open(temporary, 'wx+', 0o600)
    try {
      const expected = await writeEncrypted(input, output, Number(before.size), pathBytes, key, salt)
      await output.sync()
      const record = await readHeader(output, key)
      const actual = await readContents(output, record, key)
      if (record.originalPath !== source || !timingSafeEqual(expected, actual)) {
        throw new Error('Encrypted copy failed verification.')
      }
      if (!sameSource(before, await lstat(candidate, { bigint: true }))) {
        throw new Error('The source changed during encryption. Its path was kept.')
      }

      stop.signal.throwIfAborted()
      await link(temporary, destination)
      await syncDirectory(files)
      if (!sameSource(before, await lstat(candidate, { bigint: true }))) {
        throw new Error('The verified copy was saved, and the changed source was kept.')
      }
      stop.signal.throwIfAborted()
      try {
        await unlink(candidate)
      } catch (error) {
        throw new Error('The verified copy was saved, but the source could not be removed. ' + error.message)
      }
      print('Encrypted ' + display(name) + ' and removed its source path.')
      print('Vault file ' + display(destination))
    } finally {
      await output.close().finally(() => rm(temporary, { force: true }))
    }
  } finally {
    await input.close()
  }
}

async function encryptedEntries(key) {
  const entries = []
  const warnings = []
  const items = await readdir(files, { withFileTypes: true })
  for (const item of items) {
    if (!item.isFile() || !/^[a-f0-9]{64}\.lvlt$/u.test(item.name)) continue
    const path = join(files, item.name)
    let input
    try {
      input = await open(path, readFlags)
      const { name, size } = await readHeader(input, key)
      entries.push({ path, name, size, id: item.name.slice(0, 12) })
    } catch (error) {
      warnings.push('Skipping ' + display(item.name) + '. ' + error.message)
    } finally {
      await input?.close()
    }
  }
  entries.sort((left, right) => left.name.localeCompare(right.name) || left.id.localeCompare(right.id))
  return { entries, warnings }
}

async function checkoutFile(entry, key) {
  const input = await open(entry.path, readFlags)
  try {
    const record = await readHeader(input, key)
    // Authenticate before creating a plaintext file, and again before publishing it.
    const expected = await readContents(input, record, key)
    stop.signal.throwIfAborted()
    const restore = async (directory, destination) => {
      const staging = await mkdtemp(join(directory, '.vault-checkout-'))
      try {
        const temporary = join(staging, 'data')
        const output = await open(temporary, 'wx', 0o600)
        try {
          const actual = await readContents(input, record, key, output)
          if (!timingSafeEqual(expected, actual)) throw new Error('The encrypted file changed during checkout.')
          await output.sync()
        } finally {
          await output.close()
        }
        stop.signal.throwIfAborted()
        await link(temporary, destination)
      } finally {
        await rm(staging, { force: true, recursive: true }).catch(error => {
          console.error('Could not clean up checkout staging at ' + display(staging) + '. ' + error.message)
        })
      }
      return destination
    }

    if (record.originalPath) {
      const parent = dirname(record.originalPath)
      try {
        if (await realpath(parent) === parent && !isProtected(record.originalPath)) {
          return await restore(parent, record.originalPath)
        }
      } catch (error) {
        if (!['ENOENT', 'ENOTDIR', 'ELOOP', 'EEXIST', 'EACCES', 'EPERM', 'EROFS', 'ENOSPC',
          'EDQUOT', 'ESTALE', 'EIO', 'EXDEV', 'ENODEV', 'ENOTSUP', 'EOPNOTSUPP'].includes(error.code)) throw error
      }
      print('Original location is unavailable. Restoring to Desktop.')
    } else {
      print('This encrypted file predates path storage. Restoring to Desktop.')
    }

    const desktop = await desktopDirectory()
    try {
      return await restore(desktop, join(desktop, record.name))
    } catch (error) {
      if (error.code !== 'EEXIST') throw error
    }
    const uniqueFolder = await mkdtemp(join(desktop, 'Vault checkout-'))
    try {
      return await restore(uniqueFolder, join(uniqueFolder, record.name))
    } catch (error) {
      await rm(uniqueFolder, { force: true, recursive: true })
      throw error
    }
  } finally {
    await input.close()
  }
}

async function desktopDirectory() {
  const home = await realpath(homedir())
  let path = join(home, 'Desktop')
  if (process.platform === 'linux') {
    try {
      const { stdout } = await promisify(execFile)('xdg-user-dir', ['DESKTOP'], { timeout: 3000 })
      const configured = stdout.trimEnd()
      if (isAbsolute(configured) && configured !== home && configured !== homedir()) path = configured
    } catch {
      // A minimal Linux installation may omit xdg-user-dir.
    }
  }
  if (within(vault, path) || isProtected(path)) throw new Error('Desktop points inside the vault or project code.')
  await mkdir(path, { mode: 0o700 }).catch(error => {
    if (error.code !== 'EEXIST') throw error
  })
  const directory = await realpath(path)
  if (within(vault, directory) || isProtected(directory)) {
    throw new Error('Desktop points inside the vault or project code.')
  }
  return directory
}

function launch(path) {
  const command = process.platform === 'darwin' ? 'open' : 'xdg-open'
  return new Promise((resolveLaunch, rejectLaunch) => {
    const child = spawn(command, [path], { detached: true, stdio: 'ignore' })
    const timer = setTimeout(() => {
      child.unref()
      resolveLaunch()
    }, 500)
    child.once('error', error => {
      clearTimeout(timer)
      rejectLaunch(error)
    })
    child.once('exit', code => {
      clearTimeout(timer)
      if (code === 0) resolveLaunch()
      else rejectLaunch(new Error(command + ' failed to open the file.'))
    })
  })
}

const pageSize = 12

async function select(ask, items, label, title, context = '') {
  let page = 0
  let message = ''
  const pages = Math.max(1, Math.ceil(items.length / pageSize))
  for (;;) {
    panel(title)
    if (context) print(context)
    const visible = items.slice(page * pageSize, (page + 1) * pageSize)
    visible.forEach((item, index) => print('  [' + (index + 1) + '] ' + label(item)))
    const navigation = pages > 1
      ? '  [N] Next  [P] Previous  (' + (page + 1) + '/' + pages + ')'
      : ''
    if (navigation) print(navigation)
    if (message) print(message)
    const choice = (await ask('Select a number (Enter goes back)> ')).trim().toLowerCase()
    message = ''
    if (!choice) return null
    if (choice === 'n' && pages > 1) page = (page + 1) % pages
    else if (choice === 'p' && pages > 1) page = (page + pages - 1) % pages
    else if (/^[1-9]\d?$/u.test(choice) && Number(choice) <= visible.length) {
      return visible[Number(choice) - 1]
    } else message = 'Choose one of the listed numbers.'
  }
}

async function browse(ask) {
  let directory = await realpath(process.cwd())
  for (;;) {
    const entries = []
    for (const entry of await readdir(directory, { withFileTypes: true })) {
      const path = join(directory, entry.name)
      if (isProtected(path)) continue
      if (entry.isDirectory() || entry.isFile()) {
        entries.push({ name: entry.name, directory: entry.isDirectory(), path })
      }
    }
    entries.sort((left, right) =>
      Number(right.directory) - Number(left.directory) || left.name.localeCompare(right.name))
    if (directory === project) entries.unshift({ name: 'Checked-out files', directory: true, path: checkouts })
    entries.unshift({ name: '..', directory: true, path: dirname(directory) })
    const chosen = await select(ask, entries, entry => display(entry.name) + (entry.directory ? '/' : ''),
      'LOCAL VAULT / BROWSE', display(directory))
    if (!chosen || !chosen.directory) return chosen?.path
    directory = chosen.path
  }
}

// Finder and terminal emulators may paste a quoted path or escape its spaces.
// Parse those characters as data and never run the input through a shell.
function parsePath(line) {
  const text = line.trimStart()
  let quote = ''
  let path = ''
  let unquotedWhitespace = ''
  for (let index = 0; index < text.length; index++) {
    const character = text[index]
    if (!quote && /\s/u.test(character)) {
      unquotedWhitespace += character
      continue
    }
    path += unquotedWhitespace
    unquotedWhitespace = ''
    if (quote === character) quote = ''
    else if (!quote && (character === '"' || character === "'")) quote = character
    else if (character === '\\' && quote !== "'" && text[index + 1] !== undefined
        && (!quote || ['"', '\\', '$', '`'].includes(text[index + 1]))) {
      path += text[++index]
    } else path += character
  }
  if (quote) throw new Error('Incomplete path quoting. Use Browse or pass the file as a shell argument.')
  return text.startsWith('~/') ? homedir() + '/' + path.slice(2) : path
}

async function droppedPath(line) {
  try {
    await lstat(line)
    return line
  } catch (error) {
    if (!['ENOENT', 'ENOTDIR'].includes(error.code)) throw error
    return parsePath(line)
  }
}

async function menu(ask, key) {
  const defaults = await readPrivateJSON(optionsPath)
  let autoOpen = defaults?.autoOpen !== false
  for (;;) {
    panel('LOCAL VAULT')
    print('  Drop one file here and press Enter to encrypt and remove its source path.')
    print('  [B] Browse for a file')
    print('  [C] Check out an encrypted file')
    print('  [O] Options')
    print('  [Q] Quit')
    const input = await ask('VAULT> ')
    let showResult = false
    try {
      switch (input.trim().toLowerCase()) {
        case 'q':
          return
        case 'b': {
          const path = await browse(ask)
          if (path) {
            panel('LOCAL VAULT / ENCRYPT')
            await importFile(path, key)
            showResult = true
          }
          break
        }
        case 'c': {
          panel('LOCAL VAULT / CHECKOUT')
          const { entries, warnings } = await encryptedEntries(key)
          warnings.forEach(message => print(message))
          if (entries.length === 0) {
            print('No encrypted files available.')
            showResult = true
            break
          }
          if (warnings.length) await ask('Press Enter to view available files> ')
          const selected = await select(ask, entries, item =>
            display(item.name) + '  ' + item.size + ' B  [' + item.id + ']', 'LOCAL VAULT / CHECKOUT')
          if (!selected) break
          panel('LOCAL VAULT / CHECKOUT')
          const path = await checkoutFile(selected, key)
          print('Checked out ' + display(path))
          if (autoOpen) await launch(path)
          showResult = true
          break
        }
        case 'o': {
          panel('LOCAL VAULT / OPTIONS')
          print('  Open checked-out files automatically [' + (autoOpen ? 'ON' : 'OFF') + ']')
          if ((await ask('[T] Toggle (Enter goes back)> ')).trim().toLowerCase() === 't') {
            await savePrivateJSON(optionsPath, { autoOpen: !autoOpen }, true)
            autoOpen = !autoOpen
            panel('LOCAL VAULT / OPTIONS')
            print('Auto-open is ' + (autoOpen ? 'on.' : 'off.'))
            showResult = true
          }
          break
        }
        case '':
          break
        default:
          panel('LOCAL VAULT / ENCRYPT')
          await importFile(await droppedPath(input), key)
          showResult = true
      }
    } catch (error) {
      if (stop.signal.aborted) throw error
      console.error('Error. ' + error.message)
      showResult = true
    }
    if (showResult) await ask('Press Enter to return to the menu> ')
  }
}

function terminal() {
  let muted = false
  const output = new Writable({
    write(chunk, encoding, callback) {
      if (muted) callback()
      else process.stdout.write(chunk, encoding, callback)
    },
  })
  const readline = createInterface({ input: process.stdin, output, terminal: true, historySize: 0 })
  readline.on('SIGINT', () => stop.abort())
  readline.on('close', () => stop.abort())
  return {
    close: () => readline.close(),
    async ask(prompt, secret = false) {
      stop.signal.throwIfAborted()
      muted = secret
      if (secret) process.stdout.write(prompt)
      try {
        return await readline.question(secret ? '' : prompt, { signal: stop.signal })
      } finally {
        muted = false
        if (secret) print()
      }
    },
  }
}

const help = `Local Vault
  ./vault.sh             Open the terminal menu and initialize on first use
  ./vault.sh -- FILE     Encrypt one file and remove its source path
  ./vault.sh --reset     Erase the vault after confirmation and start setup
  ./vault.sh --help      Show this help

Checkout and auto-open settings are available in the menu.`

async function openVault(ask, reset, directImport) {
  await ensurePrivateDirectory(vault)
  if (reset && !await resetVault(ask)) return null
  await prepareVault()
  const identity = await readPrivateJSON(identityPath)
  if (!identity) {
    const key = await initialize(ask)
    if (key && !directImport) {
      try {
        await ask('Press Enter to continue> ')
      } catch (error) {
        key.fill(0)
        throw error
      }
    }
    return key
  }
  if (directImport) return unlock(ask, identity)
  for (;;) {
    panel('LOCAL VAULT / START')
    print('  [U] Unlock  [R] Reset vault  [Q] Quit')
    const choice = (await ask('Choose U, R, or Q (Enter unlocks)> ')).trim().toLowerCase()
    if (choice === 'q') return null
    if (choice === 'u' || choice === '') {
      const key = await unlock(ask, identity)
      if (key) return key
    } else if (choice === 'r') {
      if (await resetVault(ask)) return openVault(ask, false, false)
      await ask('Press Enter to return to startup> ')
    }
  }
}

async function main() {
  const args = process.argv.slice(2)
  if (args.length === 1 && ['-h', '--help'].includes(args[0])) return print(help)
  const reset = args.length === 1 && args[0] === '--reset'
  if (reset) args.shift()
  if (args[0] === '--') args.shift()
  if (args.length > 1 || args[0] === '') throw new Error('Pass one file path or run ./vault.sh --help.')
  if (Number(process.versions.node.split('.')[0]) < 22) throw new Error('Install Node.js 22 or newer.')
  if (!['darwin', 'linux'].includes(process.platform)) throw new Error('Use this utility on macOS or Linux.')
  if (!process.stdin.isTTY || !process.stdout.isTTY) {
    throw new Error('Run from an interactive terminal so credentials can be entered privately.')
  }

  await acquireSession()
  let ui
  let key
  try {
    await finishReset()
    ui = terminal()
    key = await openVault(ui.ask, reset, args.length > 0)
    if (!key) {
      if (args.length) process.exitCode = 1
      return
    }
    if (args.length) await importFile(args[0], key)
    else await menu(ui.ask, key)
  } catch (error) {
    if (!stop.signal.aborted) throw error
    process.exitCode = 130
    print('Canceled.')
  } finally {
    key?.fill(0)
    ui?.close()
    await rmdir(sessionLock)
  }
}

for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) {
  process.on(signal, () => stop.abort())
}

main().catch(error => {
  console.error('Error. ' + error.message)
  process.exitCode = 1
})
