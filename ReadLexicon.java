import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.zip.GZIPInputStream;


//class PrevRefObj {
//	public String term;
//	public int termNr;
//	
//	public PrevRefObj(String term, int termNr) {
//		this.term = term;
//		this.termNr = termNr;
//	}
//}

public class ReadLexicon {
//	private static ArrayList<Character> charList = new ArrayList<Character>(70000000);
	private static char[] charList = new char[400000000];
	private static int[] startPos = new int[35000000];
	private static int[] lenTerm = new int[35000000];
	private static int[] prevRef = new int[35000000];
	private static int[] lexBlockNr = new int[35000000];
	private static int[] lexChunkNr = new int[35000000];
	private static int[] lexPostNr = new int[35000000];
	private static int[] lexDocFreq = new int[35000000];
//	private static char[] charList = new char[4000];
//	private static int[] startPos = new int[350];
//	private static int[] lenTerm = new int[350];
//	private static int[] prevRef = new int[350];
//	private static int[] lexBlockNr = new int[350];
//	private static int[] lexChunkNr = new int[350];
//	private static int[] lexPostNr = new int[350];
//	private static int[] lexDocFreq = new int[350];
	private static int activeRefPos = 0;
	private static int cnt = 0;
	private static ArrayList<PrevRefObj> refList = new ArrayList<PrevRefObj>();
	
	private static void readLexicon(String lexiconFile) {
//		BufferedReader lexBuffer = QueryProcessor.getGzReader(new File(lexiconFile), 67108864);
		BufferedReader lexBuffer = QueryProcessor.getGzReader(new File(lexiconFile), 67108864);
//		BufferedReader lexBuffer = null;
//		try {
//			InputStream fileStream = new FileInputStream(lexiconFile);
//			Reader decoder = new InputStreamReader(fileStream);
//			lexBuffer = new BufferedReader(decoder, 67108864);
//		} catch(FileNotFoundException e) {
//			System.out.println("Error in creating gzip Buffered Reader");
//			System.exit(1);
//		}
		String line;
		String[] splitLine;
//		Store lexicon in memory
		try {
			long startTime = System.currentTimeMillis();
			int j = 0;
			while((line = lexBuffer.readLine()) != null) {
				splitLine = line.split("\t");
//				System.out.println(splitLine[0]);
				for (int p = Math.min(activeRefPos, splitLine[0].length()); p >= 3; p--) {
					
					if (refList.get(p) != null && (splitLine[0].substring(0, p)).equals(refList.get(p).term)) {
//						System.out.println("Matched Substring " + splitLine[0].substring(0, p));
//						System.out.println("Assigned PrevRef as " + refList.get(p).termNr);
//						System.out.println("Value of P is " + p);
						prevRef[cnt] = refList.get(p).termNr;
						lenTerm[cnt] = splitLine[0].length() - p;
						
						break;
					}
				}
				if (splitLine[0].length() >= 3) {
					if (refList.size() <= splitLine[0].length()) {
						for (int p = refList.size(); p <= splitLine[0].length(); p++) {
							refList.add(p, null);
						}
					}
					refList.set(splitLine[0].length(), new PrevRefObj(splitLine[0], cnt));
					activeRefPos = splitLine[0].length();
				} else {
					activeRefPos = 0;
				}
				startPos[cnt] = j;
				if (prevRef[cnt] <= 0) {
					lenTerm[cnt] = splitLine[0].length();
					prevRef[cnt] = -1;
				}
				for (int p = splitLine[0].length() - lenTerm[cnt]; p < splitLine[0].length(); p++) {
					charList[j] = splitLine[0].charAt(p);
					j++;
				}
				lexBlockNr[cnt] = Integer.parseInt(splitLine[1]);
				lexChunkNr[cnt] = Integer.parseInt(splitLine[2]);
				lexPostNr[cnt] = Integer.parseInt(splitLine[3]);
				lexDocFreq[cnt] = Integer.parseInt(splitLine[4]);
				
				cnt++;
//				if (cnt%1000000 == 0) {
//					System.out.println("Count is " + cnt);
//				}
			}
			System.out.println("Count is " + cnt);
			long endTime = System.currentTimeMillis();
			long totalTime = endTime - startTime;
			System.out.println("Time taken to read lexicon and dictionary in main memory " + totalTime);
		} catch (NumberFormatException e) {
			// TODO Auto-generated catch block
			System.out.println("Error in converting string to integer in lexicon buffer");
			System.exit(1);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			System.out.println("Error in creating lexicon buffer");
			System.exit(1);
		} 

		finally {
			try {
				lexBuffer.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
//			System.out.println("Memory " + java.lang.Runtime.getRuntime().maxMemory());
		}
	}
	
	private static termInfo searchTerm(String term) {
		int pos = searchTerm(term, 0, cnt - 1);
//		System.out.println("Position is " + pos);
		if (pos != -1) {
			return new termInfo(term, lexBlockNr[pos], lexChunkNr[pos], lexPostNr[pos], lexDocFreq[pos]);
		} else return null;
		
	}
	
	private static int searchTerm(String term, int low, int high) {
//		System.out.println("Low is " + low + "High is " + high);
		if (low > high) {
			return -1;
		}
		int mid = (low + high)/2;
//		System.out.println("Mid is " + mid);
		if (prevRef[mid] == -1) {
//			Check complete String char by char..If doesn't match then break and return whether to move right or left.
			int charPos = startPos[mid];
			for (int i = 0; i < Math.min(lenTerm[mid], term.length()); i++) {
				if (charList[charPos + i] > term.charAt(i)) {
					return searchTerm(term, low, mid - 1);
				} else if (charList[charPos + i] < term.charAt(i)) {
					return searchTerm(term, mid + 1, high);
				}
			}
			if (lenTerm[mid] < term.length()) {
				return searchTerm(term, mid + 1, high);
			} else if (lenTerm[mid] > term.length()) {
				return searchTerm(term, low, mid - 1);
			}
			return mid; //Get block nr, chunk nr and posting nr using mid position
		} else {
			ArrayList<Integer> lastPos = new ArrayList<Integer>();
			lastPos.add(mid);
			int prevRefVal = prevRef[mid];
			while (prevRefVal != -1) {
				lastPos.add(prevRefVal);
				prevRefVal = prevRef[prevRefVal];
			}
			int termJ = -1;
			for (int i = lastPos.size() - 1; i >= 0; i--) {
				for (int j = 0; j < lenTerm[lastPos.get(i)]; j++) {
					termJ++;
					if (termJ >= term.length()) {
//						System.out.println("Moved to left due to length criteria ");
						return searchTerm(term, low, mid - 1);
					}
					if (charList[startPos[lastPos.get(i)] + j] > term.charAt(termJ)) {
//						System.out.println("Moved to left");
						return searchTerm(term, low, mid - 1);
					} else if (charList[startPos[lastPos.get(i)]  + j] < term.charAt(termJ)) {
//						System.out.println("Moved to right");
						return searchTerm(term, mid + 1, high);
					}
				}
			}
			if (termJ < term.length() - 1) {
				return searchTerm(term, mid + 1, high);
			}
			return mid;
		}

		
		
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		long heapSize = Runtime.getRuntime().totalMemory();
//		System.out.println("Total Memory avaialble " + heapSize);
//		String lexiconFile = QueryProcessor.returnPath("MergeOut_2/lexicon_0~") + java.io.File.separator + "lexicon_1";
		String lexiconFile = QueryProcessor.returnPath("MergeOut_2") + java.io.File.separator + "lexicon_0";
		readLexicon(lexiconFile);

		System.out.println("Read lexicon");
//		System.out.println("Char List " + Arrays.toString(charList));
//		System.out.println("Ref List " + refList.toString());
//		System.out.println("Start Pos " + Arrays.toString(startPos));
//		System.out.println("Length " + Arrays.toString(lenTerm));
//		System.out.println("Prev Ref " + Arrays.toString(prevRef));
//		System.out.println("Block Nr " + Arrays.toString(lexBlockNr));
//		System.out.println("Chunk Nr " + Arrays.toString(lexChunkNr));
//		System.out.println("Posting Nr " + Arrays.toString(lexPostNr));
//		System.out.println("Doc Freq " + Arrays.toString(lexDocFreq));
//		termInfo t = searchTerm("jam0");
//		if (t == null) {
//			System.out.println("Term not found");
//		} else {
//			System.out.println(t.term + " BlockId " + t.blockId + " Chunk Nr " + t.chunkNr + " Posting Nr " + t.postingNr + " Doc Freq " + t.docFreq);
//		}
		
		BufferedReader lexBuffer = QueryProcessor.getGzReader(new File(lexiconFile), 67108864);
//		BufferedReader lexBuffer = null;
//		try {
//			InputStream fileStream = new FileInputStream(lexiconFile);
//			Reader decoder = new InputStreamReader(fileStream);
//			lexBuffer = new BufferedReader(decoder, 67108864);
//		} catch(FileNotFoundException e) {
//			System.out.println("Error in creating gzip Buffered Reader");
//			System.exit(1);
//		}
		String line;
		String[] splitLine;
//		Store lexicon in memory
		try {
			long startTime = System.currentTimeMillis();
			int j = 0;
			while((line = lexBuffer.readLine()) != null) {
//				System.out.println(line);
				splitLine = line.split("\t");
				termInfo t = searchTerm(splitLine[0]);
//				if (t == null) {
//					System.out.println("Term not found");
//				} else {
//					System.out.println(t.term + " BlockId " + t.blockId + " Chunk Nr " + t.chunkNr + " Posting Nr " + t.postingNr + " Doc Freq " + t.docFreq);
//				}
			}
			long endTime = System.currentTimeMillis();
			long totalTime = endTime - startTime;
			System.out.println("Time to search all terms " + totalTime);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			System.out.println("Error in reading lexicon buffer");
			System.exit(1);
		} 

		finally {
			try {
				lexBuffer.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
//			System.out.println("Memory " + java.lang.Runtime.getRuntime().maxMemory());
		}
	}

}
