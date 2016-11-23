import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;
import java.util.TreeMap;
import java.util.zip.GZIPInputStream;
import java.lang.Object;
import java.io.InputStream;

import org.apache.commons.compress.archivers.ArchiveInputStream;
import org.apache.commons.compress.archivers.ArchiveStreamFactory;
import org.apache.commons.compress.archivers.tar.TarArchiveEntry;
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream;
import org.apache.commons.compress.compressors.CompressorInputStream;
import org.apache.commons.compress.utils.IOUtils;

import java.util.zip.GZIPOutputStream;



import edu.poly.cs912.Parser;

//Class to represent posting object
class Posting {
	private int docId;
	private int freq;
	
	public Posting(int docId, int freq) {
		this.docId = docId;
		this.freq = freq;
	}
	
	int getDocId() {
		return docId;
	}
	
	int getFreq() {
		return freq;
	}
	
	public String toString() {
		return String.format(docId + ":" + freq);
	}
}

//Class to represent Page table
class DocMap {
	public int docId;
	public String url;
	public int contentLength;
	
	public DocMap(int docId, String url, int contentLength) {
		this.docId = docId;
		this.url = url;
		this.contentLength = contentLength;
	}
}

//Main class with all the functionality
public class generatePostings {
//	To print console level info
	private static boolean isDebug = true;
//  It will write both binary and ascii files
//	private static String mode = "ascii";
//Intial value for doc id and term id
	private static int DocId = 0;
	private static int termId = -1;
	private static int processedFiles = 0;
//	Maximum number of files to be used to create subindex
	private static int maxSubIndexSize = 0;
// 	Total number of subindex files created at the end of program
	private static int partialIndexCnt = 0;
	private static ArrayList<DocMap> DocUrl = new ArrayList<DocMap>();
	private static HashMap<String, Integer> termMap = new HashMap<String, Integer>();
	private static HashSet<String> httpErrorSet = new HashSet<String>();
	private static HashSet<String> stopSet = new HashSet<String>();
	private static HashMap<Integer, Integer> termCount;
//	Inverted Indexstructure
	private static HashMap<Integer, ArrayList<Posting>> invInd = new HashMap<Integer, ArrayList<Posting>>();
	
	
//	Initialize method will set maximum number of index files to be used to create subindex
//	Also it will initialize stop set to ignore all stop words
	private static void initialize(int subIndexSize) {
		maxSubIndexSize = subIndexSize;
//		Read stop word list
		URL url = Thread.currentThread().getContextClassLoader().getResource("");
		String FileName = url.getPath() + java.io.File.separator + "stopWordList";
		try {
			BufferedReader stopBr = new BufferedReader(new FileReader(FileName));
			String[] s = stopBr.readLine().split(" ");
			for (String sw : s) {
				stopSet.add(sw);
			}
			
		} catch (Exception e) {
			System.out.println(e);
		}
	}
	

	private static boolean checkForError(String content) {
		int end = content.length();
		boolean check = false;
		if (end > 300) {
			end = 300;
		}
		int ind = content.indexOf("HTTP/1.1 200 OK");

		if (ind != -1 && ind <= end) {
			return true;
		}
		ind = content.indexOf("HTTP/1.0 200 OK");
		if (ind != -1 && ind <= end) {
			return true;
		}
	// Comment Later
		httpErrorSet.add(content.substring(0, end));
//		ind = content.indexOf("HTTP/1.1");
//		if (ind != -1) {
//			int endInd = Math.min(ind + 12, content.length() - 1);
//			httpErrorSet.add(content.substring(ind, endInd));
//		}
		return false;
	}
	
//	Return byte representation of integer which is less than 128
	private static byte generateByte(int rem, int isSet) {
		byte b = (byte) rem;
		int set = (isSet << 7);
		return (byte)(b | set);
	}
	
//	After processing page, generate posting for each term found in the given page.
//	If that term is already present in inverted index then append it to existing posting array
	private static void generatePosting() {
		for (Entry<Integer, Integer> e : termCount.entrySet()) {
			Posting ps = new Posting(DocId, e.getValue());
			if (invInd.containsKey(e.getKey())) {
				ArrayList<Posting> psArray = invInd.get(e.getKey());
				psArray.add(ps);
				invInd.put(e.getKey(), psArray);
			} else {
				ArrayList<Posting> psArray = new ArrayList<Posting>();
				psArray.add(ps);
				invInd.put(e.getKey(), psArray);
			}
		}
	}
	
// Process parsed content, validate terms and increment term count
	private static void generateTermCount(String[] terms) {
//		String[] terms = content.split("\\s+");
//		System.out.println(Arrays.toString(terms));
		termCount = new HashMap<Integer, Integer>();
		for (String cTerm : terms) {
			String term = cTerm.split("\\s+")[0];
//			System.out.println(term);
			term = validateTerm(term);
			if (term != null) {
				Integer termId = getTermId(term);
				termCount.put(termId, (termCount.get(termId) == null)?1:(termCount.get(termId) + 1));				
			}
		}
	}
	
//	Returns BufferedOutput stream for given file name
	private static BufferedOutputStream getBinaryWriteBuffer(String FileName) {
		try {
			OutputStream fileStream = new FileOutputStream(FileName);
//			OutputStream gzipStream = new GZIPOutputStream(fileStream);
			return new BufferedOutputStream(fileStream, 65536);
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
		return null;
	}
	
	
//	Convert given integer to vbyte code
	public static byte[] getByteCode(int num) {
		Stack<Byte> st = new Stack<Byte>();
		byte[] bytes;
		int isSet = 0;
		while (num > 0) {
			byte b = generateByte(num % 128, isSet);
			st.add(b);
			num = num / 128;
			isSet = 1;
		}
		bytes = new byte[st.size()];
		int i = 0;
		while (st.size() > 0) {
			bytes[i] = st.pop();
			i++;
		}
		return bytes;
	}
	
	private static Integer getNextDocId() {
		return ++DocId;
	}
	
	private static Integer getNextTermId() {
		return ++termId;
	}
	
	private static Integer getTermId(String term) {
		Integer termId = termMap.get(term); 
		if (termId == null) {
			termId = getNextTermId();
			termMap.put(term, termId);
		}
		return termId;
	}
	
	// list data files which satisfies given filter from given directory
	private static File[] listFiles(String dirName, String filter) {
		File dir = new File(dirName);
		// Filter to select only data files
		FilenameFilter fileNameFilter = new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) {
				if (name.endsWith(filter)) {
					return true;
				}
				return false;
			}
		};
		if (filter.equals("")) {
			return dir.listFiles();
		} else {
			return dir.listFiles(fileNameFilter);
		}
		
	}

//	For each page in given data file, read page and generate postings for each page
	private static void processDataIndexFiles(BufferedInputStream dataBuffer, BufferedReader indexBuffer) {
		String curIndLine = null;
		int i = 0;
		try {
			while ((curIndLine = indexBuffer.readLine()) != null) {
				termCount = new HashMap<Integer, Integer>();
				String[] curIndSplit = curIndLine.split(" ");
				int length = Integer.parseInt(curIndSplit[3]);
				DocUrl.add(new DocMap(getNextDocId(), curIndSplit[0], 0));
				String[] content = readPage(dataBuffer, length, curIndSplit[0]);
				if (content != null) {
					generateTermCount(content);
					generatePosting();
				}
//				Comment Later
//				i++;
//				if (i == 7) {
//					break;
//				}
			}
		} catch(Exception e) {
			e.printStackTrace();
			System.out.println(e);
		}
	}

	private static void readCommonFiles(File[] listOfFiles) {
		processedFiles = 0;
		int cnt = 0;
		for (int i = 0; i < listOfFiles.length; i++) {
			try {
				InputStream fileStream = new FileInputStream(listOfFiles[i]);
				InputStream gzipStream = new GZIPInputStream(fileStream);
				Reader decoder = new InputStreamReader(gzipStream);
				BufferedReader inputBuffer = (new BufferedReader(decoder));
				String curIndLine;
				for (int j = 0; j < 15; j++){
					inputBuffer.readLine();
				}
				while ((curIndLine = inputBuffer.readLine()) != null) {
					if(curIndLine.trim().equals("WARC/1.0")) {
						int contentLength = 0;
						String url = null;
						for (int j = 0; j < 8; j++){
							String s = inputBuffer.readLine().trim();
							int pos;
							if ((pos = s.indexOf("WARC-Target-URI: ")) != -1) {
								url = s.substring(pos + 17);
//								System.out.println(url);
							}
							if (s.trim().startsWith("Content-Length")) {
								contentLength = Integer.parseInt((s.trim().split(":")[1]).trim());
//								System.out.println("Content Length is " + contentLength);
							}
						}
						DocUrl.add(new DocMap(getNextDocId(), url, contentLength));
						StringBuilder page = new StringBuilder();
						for (int j = 0; j <= contentLength; j++) {
							page.append((char)inputBuffer.read());
						}
//						System.out.println(page);
						if (page.length() > 0) {
							String[] pageWords = page.toString().split("\\W+");
							generateTermCount(pageWords);
							generatePosting();
						}

						
//						System.out.println(page);
						processedFiles++;
						cnt++;
//						if (cnt >= 8) {
//							break;
//						}
						if (processedFiles >= maxSubIndexSize) {
							writeTempInvIndFile();
						}

					}
				}
			} catch (Exception e) {
				// TODO: handle exception
				e.printStackTrace();
				System.out.println(e);
				System.exit(1);
			}
			System.out.println(processedFiles);
		}
		writeTempInvIndFile();
	}
	
//	Read all files one by one
//	If number of processed files reach maxSubIndex size then write inverted index to file
	private static void readDataIndexFiles(File[] listOfFiles) {
	for (int i = 0; i < listOfFiles.length; i++) {
		BufferedInputStream dataBuffer = readFile(listOfFiles[i]);
		String parentPath = listOfFiles[i].getParent();
		String dataFileNm = listOfFiles[i].getName();
		String cnt = dataFileNm.substring(0, dataFileNm.indexOf('_'));
		File indexFile = new File(parentPath + java.io.File.separator + cnt + "_index");
		BufferedReader indexBuffer = null;
		try {
			InputStream fileStream = new FileInputStream(indexFile);
			InputStream gzipStream = new GZIPInputStream(fileStream);
			Reader decoder = new InputStreamReader(gzipStream);
			indexBuffer = (new BufferedReader(decoder));
		} catch (Exception e) {
			// TODO: handle exception
			e.printStackTrace();
			System.out.println(e);
			System.exit(1);
		}
		System.out.println("Processed File " + dataFileNm);
		processDataIndexFiles(dataBuffer, indexBuffer);
		processedFiles++;
		if (processedFiles >= maxSubIndexSize) {
			writeTempInvIndFile();
		}
	}
	writeTempInvIndFile();		
}

//	Create bufferedstream for given file
	private static BufferedInputStream readFile(File fileName) {
		try {
			InputStream fileStream = new FileInputStream(fileName);
			InputStream gzipStream = new GZIPInputStream(fileStream);
			BufferedInputStream buffered = (new BufferedInputStream(gzipStream, 65536));
			return buffered;
		} catch (Exception e) {
			// TODO: handle exception
			e.printStackTrace();
			System.out.println(e);
			System.exit(1);
			return null;
		}

	}

//	Parse content of given page
	private static String[] readPage(BufferedInputStream dataBuffer, int length, String url) {
		StringBuilder s = new StringBuilder();
		try {
			for (int i = 0; i < length; i++) {
				s.append((char)dataBuffer.read());
			}		
		} catch(Exception e) {
			e.printStackTrace();
			System.out.println(e);
			System.exit(1);
		}
		if (checkForError(s.toString())) {
			StringBuilder st = new StringBuilder();
			try {
				Parser.parseDoc(url, s.toString(), st);
				String[] sSplit = st.toString().split("\n");
				return sSplit;
			} catch(Exception e) {
				System.out.println("Error in parser");
			}

		}

		return null;
	}

	// Return and create (if not exist) path of directory specified in argument
	private static String returnPath(String pathStr) {
		URL url = Thread.currentThread().getContextClassLoader().getResource("");
		String FileName = url.getPath() + java.io.File.separator + pathStr;
		File Dir = new File(FileName);
		if (!Dir.exists()) {
			try {
				Dir.mkdir();
			} catch (Exception e) {
				System.out.println(e);
				System.out.println("Error in creating Directory " + pathStr);
				System.exit(1);
			}
		}
		return FileName;
	}
	

//If term contains only special characters or term is stop word then ignore that term
	private static String validateTerm(String term) {
		
		String splChrs = "-/@?.;:\t,!<>*'\"#$%^&_+=()" ;
		if (term != null) {
			term = term.toLowerCase().trim();
			if (term.matches("[" + splChrs + "]+")) {
				return null;
			}
//			if (term.matches("^.*[^a-zA-Z0-9].*$")) {
//				if((! Character.isDigit(term.charAt(0))) && (! Character.isAlphabetic(term.charAt(0)))) {
//					term = term.substring(1);
//				} else if ((! Character.isDigit(term.charAt(term.length() - 1))) && (! Character.isAlphabetic(term.charAt(term.length() - 1)))) {
//					term = term.substring(0, term.length() - 1);
//				} else {
//					return null;
//				}
//			}
//			if (term.matches("^.*[^a-zA-Z0-9].*$")) {
//				return null;
//			}
			if (stopSet.contains(term) || term.isEmpty() || term.equals("")) {
				return null;
			}
			if (term.matches("\t")) {
				return null;
			}
		}
		return term;
	}
	
	private static BufferedWriter getBufferedWriter(String FileNamePrefix) {
		try {
			String FileName = returnPath("PostingOutput") + java.io.File.separator + FileNamePrefix + partialIndexCnt;
			OutputStream fileStream = new FileOutputStream(FileName);
			OutputStream gzipStream = new GZIPOutputStream(fileStream);
			Writer encoder = new OutputStreamWriter(gzipStream);
			return new BufferedWriter(encoder, 65536);
		} catch (Exception e) {
			System.out.println(e);
			System.out.println("Error in creating buffered writer");
			System.exit(1);
		}
		return null;
	}
	
//	Write sub inverted index to file and initialize all variables again
	private static void writeTempInvIndFile() {
		if (DocUrl.size() == 0) {
			return;
		}
		System.out.println("Writing subindex to file");
		try {
			BufferedOutputStream buffered = getBinaryWriteBuffer(returnPath("PostingOutput") +java.io.File.separator + "invIndex_" + partialIndexCnt);
			
			StringBuilder du = new StringBuilder();
			BufferedWriter docBuffered = getBufferedWriter("docUrl_");
			for (DocMap obj : DocUrl) {
				docBuffered.write(obj.docId + "\t" + obj.url + "\t" + obj.contentLength + "\n");
			}
			docBuffered.close();
			
			StringBuilder inv = new StringBuilder();
			StringBuilder lex = new StringBuilder();
			StringBuilder lexAscii = new StringBuilder();
			int lexiconAsciiPos = 0;
			int lexiconPos = 0;
			int blockId = 0;
			BufferedWriter lexBuffered = getBufferedWriter("lexicon_");
			BufferedWriter lexAsciiBuffered = getBufferedWriter("lexiconAscii_");
			BufferedWriter invAsciiBuffered = getBufferedWriter("invIndexAscii_");
			
			ArrayList<String> termsList = new ArrayList<String>(termMap.keySet());
			Collections.sort(termsList);
			for (String term : termsList) {
				int termId = termMap.get(term);
				ArrayList<Posting> ps = invInd.remove(termId);
				lexBuffered.write(term + "\t" + lexiconPos + "\t" + ps.size() + "\n");
				lexAsciiBuffered.write(term + "\t" + lexiconAsciiPos + "\t" + ps.size() + "\n");
				lexiconAsciiPos++;
				if (ps == null ){
					System.out.println(term);
				}
				int prevDocId = 0;
				for (Posting p : ps) {
					int curDocId = p.getDocId();
					invAsciiBuffered.write(curDocId - prevDocId + ":" + p.getFreq() + ",");
					byte[] docByte = getByteCode(curDocId - prevDocId);
					buffered.write(docByte);
					byte[] freqByte = getByteCode(p.getFreq());
					buffered.write(freqByte);
					lexiconPos = lexiconPos + docByte.length + freqByte.length;
					prevDocId = curDocId;
				}
				invAsciiBuffered.write("\n");
			}
			buffered.close();
			lexBuffered.close();
			lexAsciiBuffered.close();
			invAsciiBuffered.close();
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
		partialIndexCnt++;
		invInd = new HashMap<Integer, ArrayList<Posting>>();
		termMap = new HashMap<String, Integer>();
		termId = -1;
		DocId = 0;
		DocUrl = new ArrayList<DocMap>();
		processedFiles = 0;

	}
	
//	For large dataset, untar file vol* and list data files
    public static List<File> unTar(File tarFile, File directory) throws IOException {
        List<File> result = new ArrayList<File>();
        InputStream inputStream = new FileInputStream(tarFile);
        TarArchiveInputStream in = new TarArchiveInputStream(inputStream);
        TarArchiveEntry entry = in.getNextTarEntry();
        while (entry != null) {
            if (entry.isDirectory()) {
                entry = in.getNextTarEntry();
                continue;
            }
            File curfile = new File(directory, entry.getName());
            File parent = curfile.getParentFile();
            if (!parent.exists()) {
                parent.mkdirs();
            }
            OutputStream out = new FileOutputStream(curfile);
            IOUtils.copy(in, out);
            out.close();
//            result.add(entry.getName());
            if (curfile.getName().endsWith("data")) {
                result.add(curfile);
            }
            entry = in.getNextTarEntry();
        }
        in.close();
        return result;
    }
	
	public static void main(String[] args) {
		String crawlFileType = "commonCrawl";
		System.out.println("Start Time " + Calendar.getInstance().getTime());
		if (crawlFileType.equals("nz2")) {
			initialize(10);
			readDataIndexFiles(listFiles(returnPath("nz2_merged"), "data"));
		} else if (crawlFileType.equals("commonCrawl")) {
			initialize(10000);
			System.out.println(Arrays.toString(listFiles(returnPath("WetFiles"), "")));
			readCommonFiles(listFiles(returnPath("WetFiles"), ""));
		} else if (crawlFileType.equals("NZ")){
			initialize(30);
			List<File> FileList = new ArrayList<File>();
			try {
				File outputDir = new File(returnPath("NZ_UNTAR") + java.io.File.separator);
				for (File FileName : listFiles(returnPath("NZ"), "tar")) {
		            FileList.addAll(unTar(FileName, outputDir));
				}

			} catch (Exception e) {
				e.printStackTrace();
				System.out.println(e);
			}
			readDataIndexFiles(FileList.toArray(new File[FileList.size()]));
		}	
		System.out.println("End Time " + Calendar.getInstance().getTime());
	}

}
