// MergeVideoEffectLib.cpp : 定义 DLL 应用程序的导出函数。
//

#include "MergeVideoSpecialEffectLib.h"
#include <stdio.h>
#include <string>
using namespace std;
//#include<unistd.h>

#define __STDC_CONSTANT_MACROS
extern "C"{
#include "libavformat/avformat.h"
#include "libavdevice/avdevice.h"
#include "libswresample/swresample.h"
#include "libavutil/opt.h"
#include "libavutil/channel_layout.h"
	//#include "libavutil/parseutils.h"
#include "libavutil/samplefmt.h"
#include "libavutil/fifo.h"
	//#include "libavutil/internal.h"
#include "libavutil/intreadwrite.h"
#include "libavutil/dict.h"
#include "libavutil/mathematics.h"
#include "libavutil/pixdesc.h"
	//#include "libavutil/avstring.h"
	//#include "libavutil/libm.h"
#include "libavutil/imgutils.h"
#include "libavutil/timestamp.h"
#include "libavutil/bprint.h"
#include "libavutil/time.h"
#include "libavfilter/avcodec.h"
# include "libavcodec/avcodec.h"
# include "libavfilter/avfilter.h"
# include "libavfilter/buffersrc.h"
# include "libavfilter/buffersink.h"
#include "libavutil/avassert.h"
}

#define INT64_MAX        9223372036854775807i64
#define UINT64_MAX       0xffffffffffffffffui64
#define INT64_MIN        (-9223372036854775807i64 - 1)
#define AV_INPUT_BUFFER_PADDING_SIZE 32

const char program_name[] = "ffmpeg";
const int program_birth_year = 2000;

static FILE *vstats_file;

const char *const forced_keyframes_const_names[] = {
	"n",
	"n_forced",
	"prev_forced_n",
	"prev_forced_t",
	"t",
	NULL
};

static void do_video_stats(OutputStream *ost, int frame_size);
static int64_t getutime(void);
static int64_t getmaxrss(void);

static int run_as_daemon = 0;
static int nb_frames_dup = 0;
static int nb_frames_drop = 0;
static int64_t decode_error_stat[2];

static int current_time;
AVIOContext *progress_avio = NULL;

static uint8_t *subtitle_out;

InputStream **input_streams = NULL;
int        nb_input_streams = 0;
InputFile   **input_files = NULL;
int        nb_input_files = 0;

OutputStream **output_streams = NULL;
int         nb_output_streams = 0;
OutputFile   **output_files = NULL;
int         nb_output_files = 0;

FilterGraph **filtergraphs;
int        nb_filtergraphs;

#if HAVE_TERMIOS_H

/* init terminal so that we can grab keys */
static struct termios oldtty;
static int restore_tty;
#endif

#if HAVE_PTHREADS
static void free_input_threads(void);
#endif

/* sub2video hack:
Convert subtitles to video with alpha to insert them in filter graphs.
This is a temporary solution until libavfilter gets real subtitles support.
*/

static int sub2video_get_blank_frame(InputStream *ist)
{
	int ret;
	AVFrame *frame = ist->sub2video.frame;

	av_frame_unref(frame);
	ist->sub2video.frame->width = ist->sub2video.w;
	ist->sub2video.frame->height = ist->sub2video.h;
	ist->sub2video.frame->format = AV_PIX_FMT_RGB32;
	if ((ret = av_frame_get_buffer(frame, 32)) < 0)
		return ret;
	memset(frame->data[0], 0, frame->height * frame->linesize[0]);
	return 0;
}

static void sub2video_copy_rect(uint8_t *dst, int dst_linesize, int w, int h,
	AVSubtitleRect *r)
{
	uint32_t *pal, *dst2;
	uint8_t *src, *src2;
	int x, y;

	if (r->type != SUBTITLE_BITMAP) {
		av_log(NULL, AV_LOG_WARNING, "sub2video: non-bitmap subtitle\n");
		return;
	}
	if (r->x < 0 || r->x + r->w > w || r->y < 0 || r->y + r->h > h) {
		av_log(NULL, AV_LOG_WARNING, "sub2video: rectangle overflowing\n");
		return;
	}

	dst += r->y * dst_linesize + r->x * 4;
	src = r->pict.data[0];
	pal = (uint32_t *)r->pict.data[1];
	for (y = 0; y < r->h; y++) {
		dst2 = (uint32_t *)dst;
		src2 = src;
		for (x = 0; x < r->w; x++)
			*(dst2++) = pal[*(src2++)];
		dst += dst_linesize;
		src += r->pict.linesize[0];
	}
}

static void sub2video_push_ref(InputStream *ist, int64_t pts)
{
	AVFrame *frame = ist->sub2video.frame;
	int i;

	av_assert1(frame->data[0]);
	ist->sub2video.last_pts = frame->pts = pts;
	for (i = 0; i < ist->nb_filters; i++)
		av_buffersrc_add_frame_flags(ist->filters[i]->filter, frame,
		AV_BUFFERSRC_FLAG_KEEP_REF |
		AV_BUFFERSRC_FLAG_PUSH);
}

static void sub2video_update(InputStream *ist, AVSubtitle *sub)
{
	int w = ist->sub2video.w, h = ist->sub2video.h;
	AVFrame *frame = ist->sub2video.frame;
	int8_t *dst;
	int     dst_linesize;
	int num_rects, i;
	int64_t pts, end_pts;

	if (!frame)
		return;
	if (sub) {
		pts = av_rescale_q(sub->pts + sub->start_display_time * 1000LL,
		{ 1, AV_TIME_BASE }, ist->st->time_base);
		end_pts = av_rescale_q(sub->pts + sub->end_display_time * 1000LL,
		{ 1, AV_TIME_BASE }, ist->st->time_base);
		num_rects = sub->num_rects;
	}
	else {
		pts = ist->sub2video.end_pts;
		end_pts = INT64_MAX;
		num_rects = 0;
	}
	if (sub2video_get_blank_frame(ist) < 0) {
		av_log(ist->dec_ctx, AV_LOG_ERROR,
			"Impossible to get a blank canvas.\n");
		return;
	}
	dst = (int8_t *)frame->data[0];
	dst_linesize = frame->linesize[0];
	for (i = 0; i < num_rects; i++)
		sub2video_copy_rect((uint8_t *)dst, dst_linesize, w, h, sub->rects[i]);
	sub2video_push_ref(ist, pts);
	ist->sub2video.end_pts = end_pts;
}

static void sub2video_heartbeat(InputStream *ist, int64_t pts)
{
	InputFile *infile = input_files[ist->file_index];
	int i, j, nb_reqs;
	int64_t pts2;

	/* When a frame is read from a file, examine all sub2video streams in
	the same file and send the sub2video frame again. Otherwise, decoded
	video frames could be accumulating in the filter graph while a filter
	(possibly overlay) is desperately waiting for a subtitle frame. */
	for (i = 0; i < infile->nb_streams; i++) {
		InputStream *ist2 = input_streams[infile->ist_index + i];
		if (!ist2->sub2video.frame)
			continue;
		/* subtitles seem to be usually muxed ahead of other streams;
		if not, subtracting a larger time here is necessary */
		pts2 = av_rescale_q(pts, ist->st->time_base, ist2->st->time_base) - 1;
		/* do not send the heartbeat frame if the subtitle is already ahead */
		if (pts2 <= ist2->sub2video.last_pts)
			continue;
		if (pts2 >= ist2->sub2video.end_pts || !ist2->sub2video.frame->data[0])
			sub2video_update(ist2, NULL);
		for (j = 0, nb_reqs = 0; j < ist2->nb_filters; j++)
			nb_reqs += av_buffersrc_get_nb_failed_requests(ist2->filters[j]->filter);
		if (nb_reqs)
			sub2video_push_ref(ist2, pts2);
	}
}

static void sub2video_flush(InputStream *ist)
{
	int i;

	if (ist->sub2video.end_pts < INT64_MAX)
		sub2video_update(ist, NULL);
	for (i = 0; i < ist->nb_filters; i++)
		av_buffersrc_add_ref(ist->filters[i]->filter, NULL, 0);
}

/* end of sub2video hack */

static void term_exit_sigsafe(void)
{
#if HAVE_TERMIOS_H
	if (restore_tty)
		tcsetattr(0, TCSANOW, &oldtty);
#endif
}

void term_exit(void)
{
	av_log(NULL, AV_LOG_QUIET, "%s", "");
	term_exit_sigsafe();
}

static volatile int received_sigterm = 0;
static volatile int received_nb_signals = 0;
static volatile int transcode_init_done = 0;
static volatile int ffmpeg_exited = 0;
static int main_return_code = 0;

static void
sigterm_handler(int sig)
{
	received_sigterm = sig;
	received_nb_signals++;
	term_exit_sigsafe();
	if (received_nb_signals > 3) {
		//write(2, "Received > 3 system signals, hard exiting\n",
		//	strlen("Received > 3 system signals, hard exiting\n"));

		exit(123);
	}
}

#if HAVE_SETCONSOLECTRLHANDLER
static BOOL WINAPI CtrlHandler(DWORD fdwCtrlType)
{
	av_log(NULL, AV_LOG_DEBUG, "\nReceived windows signal %ld\n", fdwCtrlType);

	switch (fdwCtrlType)
	{
	case CTRL_C_EVENT:
	case CTRL_BREAK_EVENT:
		sigterm_handler(SIGINT);
		return TRUE;

	case CTRL_CLOSE_EVENT:
	case CTRL_LOGOFF_EVENT:
	case CTRL_SHUTDOWN_EVENT:
		sigterm_handler(SIGTERM);
		/* Basically, with these 3 events, when we return from this method the
		process is hard terminated, so stall as long as we need to
		to try and let the main thread(s) clean up and gracefully terminate
		(we have at most 5 seconds, but should be done far before that). */
		while (!ffmpeg_exited) {
			Sleep(0);
		}
		return TRUE;

	default:
		av_log(NULL, AV_LOG_ERROR, "Received unknown windows signal %ld\n", fdwCtrlType);
		return FALSE;
	}
}
#endif

void term_init(void)
{
#if HAVE_TERMIOS_H
	if (!run_as_daemon){
		struct termios tty;
		int istty = 1;
#if HAVE_ISATTY
		istty = isatty(0) && isatty(2);
#endif
		if (istty && tcgetattr(0, &tty) == 0) {
			oldtty = tty;
			restore_tty = 1;

			tty.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP
				| INLCR | IGNCR | ICRNL | IXON);
			tty.c_oflag |= OPOST;
			tty.c_lflag &= ~(ECHO | ECHONL | ICANON | IEXTEN);
			tty.c_cflag &= ~(CSIZE | PARENB);
			tty.c_cflag |= CS8;
			tty.c_cc[VMIN] = 1;
			tty.c_cc[VTIME] = 0;

			tcsetattr(0, TCSANOW, &tty);
		}
		signal(SIGQUIT, sigterm_handler); /* Quit (POSIX).  */
	}
#endif

	//signal(SIGINT, sigterm_handler); /* Interrupt (ANSI).    */
	//signal(SIGTERM, sigterm_handler); /* Termination (ANSI).  */
#ifdef SIGXCPU
	signal(SIGXCPU, sigterm_handler);
#endif
#if HAVE_SETCONSOLECTRLHANDLER
	SetConsoleCtrlHandler((PHANDLER_ROUTINE)CtrlHandler, TRUE);
#endif
}

/* read a key without blocking */
static int read_key(void)
{
	unsigned char ch;
#if HAVE_TERMIOS_H
	int n = 1;
	struct timeval tv;
	fd_set rfds;

	FD_ZERO(&rfds);
	FD_SET(0, &rfds);
	tv.tv_sec = 0;
	tv.tv_usec = 0;
	n = select(1, &rfds, NULL, NULL, &tv);
	if (n > 0) {
		n = read(0, &ch, 1);
		if (n == 1)
			return ch;

		return n;
	}
#elif HAVE_KBHIT
#    if HAVE_PEEKNAMEDPIPE
	static int is_pipe;
	static HANDLE input_handle;
	DWORD dw, nchars;
	if (!input_handle){
		input_handle = GetStdHandle(STD_INPUT_HANDLE);
		is_pipe = !GetConsoleMode(input_handle, &dw);
	}

	if (stdin->_cnt > 0) {
		read(0, &ch, 1);
		return ch;
	}
	if (is_pipe) {
		/* When running under a GUI, you will end here. */
		if (!PeekNamedPipe(input_handle, NULL, 0, NULL, &nchars, NULL)) {
			// input pipe may have been closed by the program that ran ffmpeg
			return -1;
		}
		//Read it
		if (nchars != 0) {
			read(0, &ch, 1);
			return ch;
		}
		else{
			return -1;
		}
	}
#    endif
	if (kbhit())
		return(getch());
#endif
	return -1;
}

static int decode_interrupt_cb(void *ctx)
{
	return received_nb_signals > transcode_init_done;
}

const AVIOInterruptCB int_cb = { decode_interrupt_cb, NULL };

static void ffmpeg_cleanup(int ret)
{
	int i, j;

	if (do_benchmark) {
		int maxrss = getmaxrss() / 1024;
		av_log(NULL, AV_LOG_INFO, "bench: maxrss=%ikB\n", maxrss);
	}

	for (i = 0; i < nb_filtergraphs; i++) {
		FilterGraph *fg = filtergraphs[i];
		avfilter_graph_free(&fg->graph);
		for (j = 0; j < fg->nb_inputs; j++) {
			av_freep(&fg->inputs[j]->name);
			av_freep(&fg->inputs[j]);
		}
		av_freep(&fg->inputs);
		for (j = 0; j < fg->nb_outputs; j++) {
			av_freep(&fg->outputs[j]->name);
			av_freep(&fg->outputs[j]);
		}
		av_freep(&fg->outputs);
		av_freep(&fg->graph_desc);

		av_freep(&filtergraphs[i]);
	}
	av_freep(&filtergraphs);

	av_freep(&subtitle_out);

	/* close files */
	for (i = 0; i < nb_output_files; i++) {
		OutputFile *of = output_files[i];
		AVFormatContext *s;
		if (!of)
			continue;
		s = of->ctx;
		if (s && s->oformat && !(s->oformat->flags & AVFMT_NOFILE))
			avio_closep(&s->pb);
		avformat_free_context(s);
		av_dict_free(&of->opts);

		av_freep(&output_files[i]);
	}
	for (i = 0; i < nb_output_streams; i++) {
		OutputStream *ost = output_streams[i];
		AVBitStreamFilterContext *bsfc;

		if (!ost)
			continue;

		bsfc = ost->bitstream_filters;
		while (bsfc) {
			AVBitStreamFilterContext *next = bsfc->next;
			av_bitstream_filter_close(bsfc);
			bsfc = next;
		}
		ost->bitstream_filters = NULL;
		av_frame_free(&ost->filtered_frame);
		av_frame_free(&ost->last_frame);

		av_parser_close(ost->parser);

		av_freep(&ost->forced_keyframes);
		av_expr_free(ost->forced_keyframes_pexpr);
		av_freep(&ost->avfilter);
		av_freep(&ost->logfile_prefix);

		av_freep(&ost->audio_channels_map);
		ost->audio_channels_mapped = 0;

		avcodec_free_context(&ost->enc_ctx);

		av_freep(&output_streams[i]);
	}
#if HAVE_PTHREADS
	free_input_threads();
#endif
	for (i = 0; i < nb_input_files; i++) {
		avformat_close_input(&input_files[i]->ctx);
		av_freep(&input_files[i]);
	}
	for (i = 0; i < nb_input_streams; i++) {
		InputStream *ist = input_streams[i];

		av_frame_free(&ist->decoded_frame);
		av_frame_free(&ist->filter_frame);
		av_dict_free(&ist->decoder_opts);
		avsubtitle_free(&ist->prev_sub.subtitle);
		av_frame_free(&ist->sub2video.frame);
		av_freep(&ist->filters);
		av_freep(&ist->hwaccel_device);

		avcodec_free_context(&ist->dec_ctx);

		av_freep(&input_streams[i]);
	}

	if (vstats_file)
		fclose(vstats_file);
	av_freep(&vstats_filename);

	av_freep(&input_streams);
	av_freep(&input_files);
	av_freep(&output_streams);
	av_freep(&output_files);

	uninit_opts();

	avformat_network_deinit();

	if (received_sigterm) {
		av_log(NULL, AV_LOG_INFO, "Exiting normally, received signal %d.\n",
			(int)received_sigterm);
	}
	else if (ret && transcode_init_done) {
		av_log(NULL, AV_LOG_INFO, "Conversion failed!\n");
	}
	term_exit();
	ffmpeg_exited = 1;
}

void remove_avoptions(AVDictionary **a, AVDictionary *b)
{
	AVDictionaryEntry *t = NULL;

	while ((t = av_dict_get(b, "", t, AV_DICT_IGNORE_SUFFIX))) {
		av_dict_set(a, t->key, NULL, AV_DICT_MATCH_CASE);
	}
}

void assert_avoptions(AVDictionary *m)
{
	AVDictionaryEntry *t;
	if ((t = av_dict_get(m, "", NULL, AV_DICT_IGNORE_SUFFIX))) {
		av_log(NULL, AV_LOG_FATAL, "Option %s not found.\n", t->key);
		exit_program(1);
	}
}

static void abort_codec_experimental(AVCodec *c, int encoder)
{
	exit_program(1);
}

static void update_benchmark(const char *fmt, ...)
{
	if (do_benchmark_all) {
		int64_t t = getutime();
		va_list va;
		char buf[1024];

		if (fmt) {
			va_start(va, fmt);
			vsnprintf(buf, sizeof(buf), fmt, va);
			va_end(va);
			av_log(NULL, AV_LOG_INFO, "bench: %I64d %s \n", t - current_time, buf);
		}
		current_time = t;
	}
}

static void close_all_output_streams(OutputStream *ost, OSTFinished this_stream, OSTFinished others)
{
	int i;
	for (i = 0; i < nb_output_streams; i++) {
		OutputStream *ost2 = output_streams[i];
		//ost2->finished |= ost == ost2 ? this_stream : others;
		if (ost == ost2)
			ost2->finished = this_stream;
		else
			ost2->finished = others;

	}
}

static void write_frame(AVFormatContext *s, AVPacket *pkt, OutputStream *ost)
{
	AVBitStreamFilterContext *bsfc = ost->bitstream_filters;
	AVCodecContext          *avctx = ost->encoding_needed ? ost->enc_ctx : ost->st->codec;
	int ret;

	if (!ost->st->codec->extradata_size && ost->enc_ctx->extradata_size) {
		ost->st->codec->extradata = (uint8_t *)av_mallocz(ost->enc_ctx->extradata_size + AV_INPUT_BUFFER_PADDING_SIZE);
		if (ost->st->codec->extradata) {
			memcpy(ost->st->codec->extradata, ost->enc_ctx->extradata, ost->enc_ctx->extradata_size);
			ost->st->codec->extradata_size = ost->enc_ctx->extradata_size;
		}
	}

	if ((avctx->codec_type == AVMEDIA_TYPE_VIDEO && video_sync_method == VSYNC_DROP) ||
		(avctx->codec_type == AVMEDIA_TYPE_AUDIO && audio_sync_method < 0))
		pkt->pts = pkt->dts = AV_NOPTS_VALUE;

	/*
	* Audio encoders may split the packets --  #frames in != #packets out.
	* But there is no reordering, so we can limit the number of output packets
	* by simply dropping them here.
	* Counting encoded video frames needs to be done separately because of
	* reordering, see do_video_out()
	*/
	if (!(avctx->codec_type == AVMEDIA_TYPE_VIDEO && avctx->codec)) {
		if (ost->frame_number >= ost->max_frames) {
			av_free_packet(pkt);
			return;
		}
		ost->frame_number++;
	}
	if (avctx->codec_type == AVMEDIA_TYPE_VIDEO) {
		int i;
		uint8_t *sd = av_packet_get_side_data(pkt, AV_PKT_DATA_SKIP_SAMPLES, NULL);
		ost->quality = sd ? AV_RL32(sd) : -1;
		ost->pict_type = sd ? sd[4] : AV_PICTURE_TYPE_NONE;

		for (i = 0; i<FF_ARRAY_ELEMS(ost->error); i++) {
			if (sd && i < sd[5])
				ost->error[i] = AV_RL64(sd + 8 + 8 * i);
			else
				ost->error[i] = -1;
		}
	}

	if (bsfc)
		av_packet_split_side_data(pkt);

	while (bsfc) {
		AVPacket new_pkt = *pkt;
		AVDictionaryEntry *bsf_arg = av_dict_get(ost->bsf_args,
			bsfc->filter->name,
			NULL, 0);
		//使用AVBitStreamFilter的时候，会调用此函数进行处理
		int a = av_bitstream_filter_filter(bsfc, avctx,
			bsf_arg ? bsf_arg->value : NULL,
			&new_pkt.data, &new_pkt.size,
			pkt->data, pkt->size,
			pkt->flags & AV_PKT_FLAG_KEY);
		if (a == 0 && new_pkt.data != pkt->data) {
			uint8_t *t = (uint8_t *)av_malloc(new_pkt.size + AV_INPUT_BUFFER_PADDING_SIZE); //the new should be a subset of the old so cannot overflow
			if (t) {
				memcpy(t, new_pkt.data, new_pkt.size);
				memset(t + new_pkt.size, 0, AV_INPUT_BUFFER_PADDING_SIZE);
				new_pkt.data = t;
				new_pkt.buf = NULL;
				a = 1;
			}
			else
				a = AVERROR(ENOMEM);
		}
		if (a > 0) {
			pkt->side_data = NULL;
			pkt->side_data_elems = 0;
			av_free_packet(pkt);
			new_pkt.buf = av_buffer_create(new_pkt.data, new_pkt.size,
				av_buffer_default_free, NULL, 0);
			if (!new_pkt.buf)
				exit_program(1);
		}
		else if (a < 0) {
			new_pkt = *pkt;
			av_log(NULL, AV_LOG_ERROR, "Failed to open bitstream filter %s for stream %d with codec %s",
				bsfc->filter->name, pkt->stream_index,
				avctx->codec ? avctx->codec->name : "copy");
			print_error("", a);
			if (exit_on_error)
				exit_program(1);
		}
		*pkt = new_pkt;

		bsfc = bsfc->next;
	}

	if (!(s->oformat->flags & AVFMT_NOTIMESTAMPS)) {
		if (pkt->dts != AV_NOPTS_VALUE &&
			pkt->pts != AV_NOPTS_VALUE &&
			pkt->dts > pkt->pts) {
			av_log(s, AV_LOG_WARNING, "Invalid DTS: % PTS: %I64d in output stream %d:%d, replacing by guess\n",
				pkt->dts, pkt->pts,
				ost->file_index, ost->st->index);
			pkt->pts =
				pkt->dts = pkt->pts + pkt->dts + ost->last_mux_dts + 1
				- FFMIN3(pkt->pts, pkt->dts, ost->last_mux_dts + 1)
				- FFMAX3(pkt->pts, pkt->dts, ost->last_mux_dts + 1);
		}
		if (
			(avctx->codec_type == AVMEDIA_TYPE_AUDIO || avctx->codec_type == AVMEDIA_TYPE_VIDEO) &&
			pkt->dts != AV_NOPTS_VALUE &&
			ost->last_mux_dts != AV_NOPTS_VALUE) {
			int64_t max = ost->last_mux_dts + !(s->oformat->flags & AVFMT_TS_NONSTRICT);
			if (pkt->dts < max) {
				int loglevel = max - pkt->dts > 2 || avctx->codec_type == AVMEDIA_TYPE_VIDEO ? AV_LOG_WARNING : AV_LOG_DEBUG;
				av_log(s, loglevel, "Non-monotonous DTS in output stream "
					"%d:%d; previous: %I64d, current: %I64d",
					ost->file_index, ost->st->index, ost->last_mux_dts, pkt->dts);
				if (exit_on_error) {
					av_log(NULL, AV_LOG_FATAL, "aborting.\n");
					exit_program(1);
				}
				av_log(s, loglevel, "changing to %I64d. This may result "
					"in incorrect timestamps in the output file.\n",
					max);
				if (pkt->pts >= pkt->dts)
					pkt->pts = FFMAX(pkt->pts, max);
				pkt->dts = max;
			}
		}
	}
	ost->last_mux_dts = pkt->dts;

	ost->data_size += pkt->size;
	ost->packets_written++;

	pkt->stream_index = ost->index;

	if (debug_ts) {
		av_log(NULL, AV_LOG_INFO, "muxer <- type:%s "
			"pkt_pts:%s pkt_pts_time:%s pkt_dts:%s pkt_dts_time:%s size:%d\n",
			av_get_media_type_string(ost->enc_ctx->codec_type),
			av_ts2str(pkt->pts), av_ts2timestr(pkt->pts, &ost->st->time_base),
			av_ts2str(pkt->dts), av_ts2timestr(pkt->dts, &ost->st->time_base),
			pkt->size
			);
	}

	ret = av_interleaved_write_frame(s, pkt);    //写入压缩编码数据
	if (ret < 0) {
		print_error("av_interleaved_write_frame()", ret);
		main_return_code = 1;
		close_all_output_streams(ost, (OSTFinished)(MUXER_FINISHED | ENCODER_FINISHED), ENCODER_FINISHED);
	}
	av_free_packet(pkt);
}

static void close_output_stream(OutputStream *ost)
{
	OutputFile *of = output_files[ost->file_index];

	ost->finished = ENCODER_FINISHED;
	if (of->shortest) {
		int64_t end = av_rescale_q(ost->sync_opts - ost->first_pts, ost->enc_ctx->time_base, { 1, AV_TIME_BASE });
		of->recording_time = FFMIN(of->recording_time, end);
	}
}

static int check_recording_time(OutputStream *ost)
{
	OutputFile *of = output_files[ost->file_index];

	if (of->recording_time != INT64_MAX &&
		av_compare_ts(ost->sync_opts - ost->first_pts, ost->enc_ctx->time_base, of->recording_time,
		{ 1, AV_TIME_BASE }) >= 0) {
		close_output_stream(ost);
		return 0;
	}
	return 1;
}

static void do_audio_out(AVFormatContext *s, OutputStream *ost,
	AVFrame *frame)
{
	AVCodecContext *enc = ost->enc_ctx;
	AVPacket pkt;
	int got_packet = 0;

	av_init_packet(&pkt);
	pkt.data = NULL;
	pkt.size = 0;

	if (!check_recording_time(ost))
		return;

	if (frame->pts == AV_NOPTS_VALUE || audio_sync_method < 0)
		frame->pts = ost->sync_opts;
	ost->sync_opts = frame->pts + frame->nb_samples;
	ost->samples_encoded += frame->nb_samples;
	ost->frames_encoded++;

	av_assert0(pkt.size || !pkt.data);
	update_benchmark(NULL);
	if (debug_ts) {
		av_log(NULL, AV_LOG_INFO, "encoder <- type:audio "
			"frame_pts:%s frame_pts_time:%s time_base:%d/%d\n",
			av_ts2str(frame->pts), av_ts2timestr(frame->pts, &enc->time_base),
			enc->time_base.num, enc->time_base.den);
	}

	if (avcodec_encode_audio2(enc, &pkt, frame, &got_packet) < 0) {
		av_log(NULL, AV_LOG_FATAL, "Audio encoding failed (avcodec_encode_audio2)\n");
		exit_program(1);
	}
	update_benchmark("encode_audio %d.%d", ost->file_index, ost->index);

	if (got_packet) {
		av_packet_rescale_ts(&pkt, enc->time_base, ost->st->time_base);

		if (debug_ts) {
			av_log(NULL, AV_LOG_INFO, "encoder -> type:audio "
				"pkt_pts:%s pkt_pts_time:%s pkt_dts:%s pkt_dts_time:%s\n",
				av_ts2str(pkt.pts), av_ts2timestr(pkt.pts, &ost->st->time_base),
				av_ts2str(pkt.dts), av_ts2timestr(pkt.dts, &ost->st->time_base));
		}

		write_frame(s, &pkt, ost);
	}
}

static void do_subtitle_out(AVFormatContext *s,
	OutputStream *ost,
	InputStream *ist,
	AVSubtitle *sub)
{
	int subtitle_out_max_size = 1024 * 1024;
	int subtitle_out_size, nb, i;
	AVCodecContext *enc;
	AVPacket pkt;
	int64_t pts;

	if (sub->pts == AV_NOPTS_VALUE) {
		av_log(NULL, AV_LOG_ERROR, "Subtitle packets must have a pts\n");
		if (exit_on_error)
			exit_program(1);
		return;
	}

	enc = ost->enc_ctx;

	if (!subtitle_out) {
		subtitle_out = (uint8_t *)av_malloc(subtitle_out_max_size);
		if (!subtitle_out) {
			av_log(NULL, AV_LOG_FATAL, "Failed to allocate subtitle_out\n");
			exit_program(1);
		}
	}

	/* Note: DVB subtitle need one packet to draw them and one other
	packet to clear them */
	/* XXX: signal it in the codec context ? */
	if (enc->codec_id == AV_CODEC_ID_DVB_SUBTITLE)
		nb = 2;
	else
		nb = 1;

	/* shift timestamp to honor -ss and make check_recording_time() work with -t */
	pts = sub->pts;
	if (output_files[ost->file_index]->start_time != AV_NOPTS_VALUE)
		pts -= output_files[ost->file_index]->start_time;
	for (i = 0; i < nb; i++) {
		unsigned save_num_rects = sub->num_rects;

		ost->sync_opts = av_rescale_q(pts, { 1, AV_TIME_BASE }, enc->time_base);
		if (!check_recording_time(ost))
			return;

		sub->pts = pts;
		// start_display_time is required to be 0
		sub->pts += av_rescale_q(sub->start_display_time, { 1, 1000 }, { 1, AV_TIME_BASE });
		sub->end_display_time -= sub->start_display_time;
		sub->start_display_time = 0;
		if (i == 1)
			sub->num_rects = 0;

		ost->frames_encoded++;

		subtitle_out_size = avcodec_encode_subtitle(enc, subtitle_out,
			subtitle_out_max_size, sub);
		if (i == 1)
			sub->num_rects = save_num_rects;
		if (subtitle_out_size < 0) {
			av_log(NULL, AV_LOG_FATAL, "Subtitle encoding failed\n");
			exit_program(1);
		}

		av_init_packet(&pkt);
		pkt.data = subtitle_out;
		pkt.size = subtitle_out_size;
		pkt.pts = av_rescale_q(sub->pts, { 1, AV_TIME_BASE }, ost->st->time_base);
		pkt.duration = av_rescale_q(sub->end_display_time, { 1, 1000 }, ost->st->time_base);
		if (enc->codec_id == AV_CODEC_ID_DVB_SUBTITLE) {
			/* XXX: the pts correction is handled here. Maybe handling
			it in the codec would be better */
			if (i == 0)
				pkt.pts += 90 * sub->start_display_time;
			else
				pkt.pts += 90 * sub->end_display_time;
		}
		pkt.dts = pkt.pts;
		write_frame(s, &pkt, ost);
	}
}
int mid_pred(int a, int b, int c)
{
	if (a>b){
		if (c>b){
			if (c>a) b = a;
			else    b = c;
		}
	}
	else{
		if (b>c){
			if (c>a) b = c;
			else    b = a;
		}
	}
	return b;
}

static void do_video_out(AVFormatContext *s,
	OutputStream *ost,
	AVFrame *next_picture,
	double sync_ipts)
{
	int ret, format_video_sync;
	AVPacket pkt;
	AVCodecContext *enc = ost->enc_ctx;
	AVCodecContext *mux_enc = ost->st->codec;
	int nb_frames, nb0_frames, i;
	double delta, delta0;
	double duration = 0;
	int frame_size = 0;
	InputStream *ist = NULL;
	AVFilterContext *filter = ost->filter->filter;

	if (ost->source_index >= 0)
		ist = input_streams[ost->source_index];

	if (filter->inputs[0]->frame_rate.num > 0 &&
		filter->inputs[0]->frame_rate.den > 0)
		duration = 1 / (av_q2d(filter->inputs[0]->frame_rate) * av_q2d(enc->time_base));

	if (ist && ist->st->start_time != AV_NOPTS_VALUE && ist->st->first_dts != AV_NOPTS_VALUE && ost->frame_rate.num)
		duration = FFMIN(duration, 1 / (av_q2d(ost->frame_rate) * av_q2d(enc->time_base)));

	if (!ost->filters_script &&
		!ost->filters &&
		next_picture &&
		ist &&
		lrintf(av_frame_get_pkt_duration(next_picture) * av_q2d(ist->st->time_base) / av_q2d(enc->time_base)) > 0) {
		duration = lrintf(av_frame_get_pkt_duration(next_picture) * av_q2d(ist->st->time_base) / av_q2d(enc->time_base));
	}

	if (!next_picture) {
		//end, flushing
		nb0_frames = nb_frames = mid_pred(ost->last_nb0_frames[0],
			ost->last_nb0_frames[1],
			ost->last_nb0_frames[2]);
	}
	else {
		delta0 = sync_ipts - ost->sync_opts;
		delta = delta0 + duration;

		/* by default, we output a single frame */
		nb0_frames = 0;
		nb_frames = 1;

		format_video_sync = video_sync_method;
		if (format_video_sync == VSYNC_AUTO) {
			if (!strcmp(s->oformat->name, "avi")) {
				format_video_sync = VSYNC_VFR;
			}
			else
				format_video_sync = (s->oformat->flags & AVFMT_VARIABLE_FPS) ? ((s->oformat->flags & AVFMT_NOTIMESTAMPS) ? VSYNC_PASSTHROUGH : VSYNC_VFR) : VSYNC_CFR;
			if (ist
				&& format_video_sync == VSYNC_CFR
				&& input_files[ist->file_index]->ctx->nb_streams == 1
				&& input_files[ist->file_index]->input_ts_offset == 0) {
				format_video_sync = VSYNC_VSCFR;
			}
			if (format_video_sync == VSYNC_CFR && copy_ts) {
				format_video_sync = VSYNC_VSCFR;
			}
		}

		if (delta0 < 0 &&
			delta > 0 &&
			format_video_sync != VSYNC_PASSTHROUGH &&
			format_video_sync != VSYNC_DROP) {
			double cor = FFMIN(-delta0, duration);
			if (delta0 < -0.6) {
				av_log(NULL, AV_LOG_WARNING, "Past duration %f too large\n", -delta0);
			}
			else
				av_log(NULL, AV_LOG_DEBUG, "Cliping frame in rate conversion by %f\n", -delta0);
			sync_ipts += cor;
			duration -= cor;
			delta0 += cor;
		}

		switch (format_video_sync) {
		case VSYNC_VSCFR:
			if (ost->frame_number == 0 && delta - duration >= 0.5) {
				av_log(NULL, AV_LOG_DEBUG, "Not duplicating %d initial frames\n", (int)lrintf(delta - duration));
				delta = duration;
				delta0 = 0;
				ost->sync_opts = lrint(sync_ipts);
			}
		case VSYNC_CFR:
			// FIXME set to 0.5 after we fix some dts/pts bugs like in avidec.c
			if (frame_drop_threshold && delta < frame_drop_threshold && ost->frame_number) {
				nb_frames = 0;
			}
			else if (delta < -1.1)
				nb_frames = 0;
			else if (delta > 1.1) {
				nb_frames = lrintf(delta);
				if (delta0 > 1.1)
					nb0_frames = lrintf(delta0 - 0.6);
			}
			break;
		case VSYNC_VFR:
			if (delta <= -0.6)
				nb_frames = 0;
			else if (delta > 0.6)
				ost->sync_opts = lrint(sync_ipts);
			break;
		case VSYNC_DROP:
		case VSYNC_PASSTHROUGH:
			ost->sync_opts = lrint(sync_ipts);
			break;
		default:
			av_assert0(0);
		}
	}

	nb_frames = FFMIN(nb_frames, ost->max_frames - ost->frame_number);
	nb0_frames = FFMIN(nb0_frames, nb_frames);

	memmove(ost->last_nb0_frames + 1,
		ost->last_nb0_frames,
		sizeof(ost->last_nb0_frames[0]) * (FF_ARRAY_ELEMS(ost->last_nb0_frames) - 1));
	ost->last_nb0_frames[0] = nb0_frames;

	if (nb0_frames == 0 && ost->last_droped) {
		nb_frames_drop++;
		av_log(NULL, AV_LOG_VERBOSE,
			"*** dropping frame %d from stream %d at ts %I64d\n",
			ost->frame_number, ost->st->index, ost->last_frame->pts);
	}
	if (nb_frames > (nb0_frames && ost->last_droped) + (nb_frames > nb0_frames)) {
		if (nb_frames > dts_error_threshold * 30) {
			av_log(NULL, AV_LOG_ERROR, "%d frame duplication too large, skipping\n", nb_frames - 1);
			nb_frames_drop++;
			return;
		}
		nb_frames_dup += nb_frames - (nb0_frames && ost->last_droped) - (nb_frames > nb0_frames);
		av_log(NULL, AV_LOG_VERBOSE, "*** %d dup!\n", nb_frames - 1);
	}
	ost->last_droped = nb_frames == nb0_frames && next_picture;

	/* duplicates frame if needed */
	for (i = 0; i < nb_frames; i++) {
		AVFrame *in_picture;
		av_init_packet(&pkt);
		pkt.data = NULL;
		pkt.size = 0;

		if (i < nb0_frames && ost->last_frame) {
			in_picture = ost->last_frame;
		}
		else
			in_picture = next_picture;

		if (!in_picture)
			return;

		in_picture->pts = ost->sync_opts;

#if 1
		if (!check_recording_time(ost))
#else
		if (ost->frame_number >= ost->max_frames)
#endif
			return;

		if (s->oformat->flags & AVFMT_RAWPICTURE &&
			enc->codec->id == AV_CODEC_ID_RAWVIDEO) {
			/* raw pictures are written as AVPicture structure to
			avoid any copies. We support temporarily the older
			method. */
			if (in_picture->interlaced_frame)
				mux_enc->field_order = in_picture->top_field_first ? AV_FIELD_TB : AV_FIELD_BT;
			else
				mux_enc->field_order = AV_FIELD_PROGRESSIVE;
			pkt.data = (uint8_t *)in_picture;
			pkt.size = sizeof(AVPicture);
			pkt.pts = av_rescale_q(in_picture->pts, enc->time_base, ost->st->time_base);
			pkt.flags |= AV_PKT_FLAG_KEY;

			write_frame(s, &pkt, ost);
		}
		else {
			int got_packet, forced_keyframe = 0;
			double pts_time;

			if (enc->flags & (CODEC_FLAG_INTERLACED_DCT | CODEC_FLAG_INTERLACED_ME) &&
				ost->top_field_first >= 0)
				in_picture->top_field_first = !!ost->top_field_first;

			if (in_picture->interlaced_frame) {
				if (enc->codec->id == AV_CODEC_ID_MJPEG)
					mux_enc->field_order = in_picture->top_field_first ? AV_FIELD_TT : AV_FIELD_BB;
				else
					mux_enc->field_order = in_picture->top_field_first ? AV_FIELD_TB : AV_FIELD_BT;
			}
			else
				mux_enc->field_order = AV_FIELD_PROGRESSIVE;

			in_picture->quality = enc->global_quality;
			in_picture->pict_type = (AVPictureType)0;

			pts_time = in_picture->pts != AV_NOPTS_VALUE ?
				in_picture->pts * av_q2d(enc->time_base) : NAN;
			if (ost->forced_kf_index < ost->forced_kf_count &&
				in_picture->pts >= ost->forced_kf_pts[ost->forced_kf_index]) {
				ost->forced_kf_index++;
				forced_keyframe = 1;
			}
			else if (ost->forced_keyframes_pexpr) {
				double res;
				ost->forced_keyframes_expr_const_values[FKF_T] = pts_time;
				res = av_expr_eval(ost->forced_keyframes_pexpr,
					ost->forced_keyframes_expr_const_values, NULL);
				av_dlog(NULL, "force_key_frame: n:%f n_forced:%f prev_forced_n:%f t:%f prev_forced_t:%f -> res:%f\n",
					ost->forced_keyframes_expr_const_values[FKF_N],
					ost->forced_keyframes_expr_const_values[FKF_N_FORCED],
					ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_N],
					ost->forced_keyframes_expr_const_values[FKF_T],
					ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_T],
					res);
				if (res) {
					forced_keyframe = 1;
					ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_N] =
						ost->forced_keyframes_expr_const_values[FKF_N];
					ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_T] =
						ost->forced_keyframes_expr_const_values[FKF_T];
					ost->forced_keyframes_expr_const_values[FKF_N_FORCED] += 1;
				}

				ost->forced_keyframes_expr_const_values[FKF_N] += 1;
			}
			else if (ost->forced_keyframes
				&& !strncmp((const char *)ost->forced_keyframes, "source", 6)
				&& in_picture->key_frame == 1) {
				forced_keyframe = 1;
			}

			if (forced_keyframe) {
				in_picture->pict_type = AV_PICTURE_TYPE_I;
				av_log(NULL, AV_LOG_DEBUG, "Forced keyframe at time %f\n", pts_time);
			}

			update_benchmark(NULL);
			if (debug_ts) {
				av_log(NULL, AV_LOG_INFO, "encoder <- type:video "
					"frame_pts:%s frame_pts_time:%s time_base:%d/%d\n",
					av_ts2str(in_picture->pts), av_ts2timestr(in_picture->pts, &enc->time_base),
					enc->time_base.num, enc->time_base.den);
			}

			ost->frames_encoded++;

			ret = avcodec_encode_video2(enc, &pkt, in_picture, &got_packet);  //编码一帧视频,编码前数据in_picture
			update_benchmark("encode_video %d.%d", ost->file_index, ost->index);
			if (ret < 0) {
				av_log(NULL, AV_LOG_FATAL, "Video encoding failed\n");
				exit_program(1);
			}

			if (got_packet) {
				if (debug_ts) {
					av_log(NULL, AV_LOG_INFO, "encoder -> type:video "
						"pkt_pts:%s pkt_pts_time:%s pkt_dts:%s pkt_dts_time:%s\n",
						av_ts2str(pkt.pts), av_ts2timestr(pkt.pts, &enc->time_base),
						av_ts2str(pkt.dts), av_ts2timestr(pkt.dts, &enc->time_base));
				}

				if (pkt.pts == AV_NOPTS_VALUE && !(enc->codec->capabilities & CODEC_CAP_DELAY))
					pkt.pts = ost->sync_opts;

				av_packet_rescale_ts(&pkt, enc->time_base, ost->st->time_base);

				if (debug_ts) {
					av_log(NULL, AV_LOG_INFO, "encoder -> type:video "
						"pkt_pts:%s pkt_pts_time:%s pkt_dts:%s pkt_dts_time:%s\n",
						av_ts2str(pkt.pts), av_ts2timestr(pkt.pts, &ost->st->time_base),
						av_ts2str(pkt.dts), av_ts2timestr(pkt.dts, &ost->st->time_base));
				}

				frame_size = pkt.size;
				write_frame(s, &pkt, ost);  //在这里实现分割处理

				/* if two pass, output log */
				if (ost->logfile && enc->stats_out) {
					fprintf(ost->logfile, "%s", enc->stats_out);
				}
			}
		}
		ost->sync_opts++;
		/*
		* For video, number of frames in == number of packets out.
		* But there may be reordering, so we can't throw away frames on encoder
		* flush, we need to limit them here, before they go into encoder.
		*/
		ost->frame_number++;

		if (vstats_filename && frame_size)
			do_video_stats(ost, frame_size);
	}

	if (!ost->last_frame)
		ost->last_frame = av_frame_alloc();
	av_frame_unref(ost->last_frame);
	if (next_picture && ost->last_frame)
		av_frame_ref(ost->last_frame, next_picture);
	else
		av_frame_free(&ost->last_frame);
}

static double psnr(double d)
{
	return -10.0 * log(d) / log(10.0);
}

static void do_video_stats(OutputStream *ost, int frame_size)
{
	AVCodecContext *enc;
	int frame_number;
	double ti1, bitrate, avg_bitrate;

	/* this is executed just the first time do_video_stats is called */
	if (!vstats_file) {
		vstats_file = fopen(vstats_filename, "w");
		if (!vstats_file) {
			perror("fopen");
			exit_program(1);
		}
	}

	enc = ost->enc_ctx;
	if (enc->codec_type == AVMEDIA_TYPE_VIDEO) {
		frame_number = ost->st->nb_frames;
		fprintf(vstats_file, "frame= %5d q= %2.1f ", frame_number,
			ost->quality / (float)FF_QP2LAMBDA);

		if (ost->error[0] >= 0 && (enc->flags & CODEC_FLAG_PSNR))
			fprintf(vstats_file, "PSNR= %6.2f ", psnr(ost->error[0] / (enc->width * enc->height * 255.0 * 255.0)));

		fprintf(vstats_file, "f_size= %6d ", frame_size);
		/* compute pts value */
		ti1 = av_stream_get_end_pts(ost->st) * av_q2d(ost->st->time_base);
		if (ti1 < 0.01)
			ti1 = 0.01;

		bitrate = (frame_size * 8) / av_q2d(enc->time_base) / 1000.0;
		avg_bitrate = (double)(ost->data_size * 8) / ti1 / 1000.0;
		fprintf(vstats_file, "s_size= %8.0fkB time= %0.3f br= %7.1fkbits/s avg_br= %7.1fkbits/s ",
			(double)ost->data_size / 1024, ti1, bitrate, avg_bitrate);
		fprintf(vstats_file, "type= %c\n", av_get_picture_type_char((AVPictureType)ost->pict_type));
	}
}

static void finish_output_stream(OutputStream *ost)
{
	OutputFile *of = output_files[ost->file_index];
	int i;

	ost->finished = (OSTFinished)(ENCODER_FINISHED + MUXER_FINISHED);

	if (of->shortest) {
		for (i = 0; i < of->ctx->nb_streams; i++)
			output_streams[of->ost_index + i]->finished = (OSTFinished)(ENCODER_FINISHED | MUXER_FINISHED);
	}
}

/**
* Get and encode new output from any of the filtergraphs, without causing
* activity.
*
* @return  0 for success, <0 for severe errors
*/
static int reap_filters(int flush)
{
	AVFrame *filtered_frame = NULL;
	int i;

	/* Reap all buffers present in the buffer sinks 获得当前在缓冲池中的所有缓存*/
	for (i = 0; i < nb_output_streams; i++) {   //nb_output_streams 视频 音频等总数，测试中这里循环了两次
		OutputStream *ost = output_streams[i];    //循环每个输出流
		OutputFile    *of = output_files[ost->file_index];   //输出流对应的输出文件
		AVFilterContext *filter;
		AVCodecContext *enc = ost->enc_ctx;
		int ret = 0;

		if (!ost->filter)
			continue;
		filter = ost->filter->filter;

		if (!ost->filtered_frame && !(ost->filtered_frame = av_frame_alloc())) {
			return AVERROR(ENOMEM);
		}
		filtered_frame = ost->filtered_frame;

		while (1) {   //举例说明：当前输出流为视频，并且视频有输出帧，则这个循环了两次，一次处理输出帧，一次进入发现没有可输出的帧，则退出这个循环。
			//        接着根据上面的for循环，当前输出流为音频，但音频帧没有实际的输出帧，则这个循环只是进入了，立即也就退出了。

			double float_pts = AV_NOPTS_VALUE; // this is identical to filtered_frame.pts but with higher precision
			//从AVFilterContext中取出一帧解码后的数据（结构为AVFilterBufferRef，可以转换为AVFrame）

			ret = av_buffersink_get_frame_flags(filter, filtered_frame,
				AV_BUFFERSINK_FLAG_NO_REQUEST);
			if (ret < 0) {   //会进入，用于退出while循环的
				if (ret != AVERROR(EAGAIN) && ret != AVERROR_EOF) {
					av_log(NULL, AV_LOG_WARNING,
						"Error in av_buffersink_get_frame_flags(): %s\n", av_err2str(ret));
				}
				else if (flush && ret == AVERROR_EOF) {
					if (filter->inputs[0]->type == AVMEDIA_TYPE_VIDEO)
						do_video_out(of->ctx, ost, NULL, AV_NOPTS_VALUE);
				}
				break;
			}
			if (ost->finished) {
				av_frame_unref(filtered_frame);
				continue;
			}
			if (filtered_frame->pts != AV_NOPTS_VALUE) {
				int64_t start_time = (of->start_time == AV_NOPTS_VALUE) ? 0 : of->start_time;
				AVRational tb = enc->time_base;
				int extra_bits = av_clip(29 - av_log2(tb.den), 0, 16);

				tb.den <<= extra_bits;
				float_pts =
					av_rescale_q(filtered_frame->pts, filter->inputs[0]->time_base, tb) -
					av_rescale_q(start_time, { 1, AV_TIME_BASE }, tb);
				float_pts /= 1 << extra_bits;
				// avoid exact midoints to reduce the chance of rounding differences, this can be removed in case the fps code is changed to work with integers
				float_pts += FFSIGN(float_pts) * 1.0 / (1 << 17);

				filtered_frame->pts =
					av_rescale_q(filtered_frame->pts, filter->inputs[0]->time_base, enc->time_base) -
					av_rescale_q(start_time, { 1, AV_TIME_BASE }, enc->time_base);
			}
			//if (ost->source_index >= 0)
			//    *filtered_frame= *input_streams[ost->source_index]->decoded_frame; //for me_threshold

			switch (filter->inputs[0]->type) {
			case AVMEDIA_TYPE_VIDEO:
				if (!ost->frame_aspect_ratio.num)
					enc->sample_aspect_ratio = filtered_frame->sample_aspect_ratio;

				if (debug_ts) {
					av_log(NULL, AV_LOG_INFO, "filter -> pts:%s pts_time:%s exact:%f time_base:%d/%d\n",
						av_ts2str(filtered_frame->pts), av_ts2timestr(filtered_frame->pts, &enc->time_base),
						float_pts,
						enc->time_base.num, enc->time_base.den);
				}

				do_video_out(of->ctx, ost, filtered_frame, float_pts);
				break;
			case AVMEDIA_TYPE_AUDIO:
				if (!(enc->codec->capabilities & CODEC_CAP_PARAM_CHANGE) &&
					enc->channels != av_frame_get_channels(filtered_frame)) {
					av_log(NULL, AV_LOG_ERROR,
						"Audio filter graph output is not normalized and encoder does not support parameter changes\n");
					break;
				}
				do_audio_out(of->ctx, ost, filtered_frame);
				break;
			default:
				// TODO support subtitle filters
				av_assert0(0);
			}

			av_frame_unref(filtered_frame);   //释放资源
		}
	}

	return 0;
}

static void print_final_stats(int64_t total_size)
{
	uint64_t video_size = 0, audio_size = 0, extra_size = 0, other_size = 0;
	uint64_t subtitle_size = 0;
	uint64_t data_size = 0;
	float percent = -1.0;
	int i, j;
	int pass1_used = 1;

	for (i = 0; i < nb_output_streams; i++) {
		OutputStream *ost = output_streams[i];
		switch (ost->enc_ctx->codec_type) {
		case AVMEDIA_TYPE_VIDEO: video_size += ost->data_size; break;
		case AVMEDIA_TYPE_AUDIO: audio_size += ost->data_size; break;
		case AVMEDIA_TYPE_SUBTITLE: subtitle_size += ost->data_size; break;
		default:                 other_size += ost->data_size; break;
		}
		extra_size += ost->enc_ctx->extradata_size;
		data_size += ost->data_size;
		if ((ost->enc_ctx->flags & (CODEC_FLAG_PASS1 | CODEC_FLAG_PASS2))
			!= CODEC_FLAG_PASS1)
			pass1_used = 0;
	}

	if (data_size && total_size>0 && total_size >= data_size)
		percent = 100.0 * (total_size - data_size) / data_size;

	av_log(NULL, AV_LOG_INFO, "video:%1.0fkB audio:%1.0fkB subtitle:%1.0fkB other streams:%1.0fkB global headers:%1.0fkB muxing overhead: ",
		video_size / 1024.0,
		audio_size / 1024.0,
		subtitle_size / 1024.0,
		other_size / 1024.0,
		extra_size / 1024.0);
	if (percent >= 0.0)
		av_log(NULL, AV_LOG_INFO, "%f%%", percent);
	else
		av_log(NULL, AV_LOG_INFO, "unknown");
	av_log(NULL, AV_LOG_INFO, "\n");

	/* print verbose per-stream stats */
	for (i = 0; i < nb_input_files; i++) {
		InputFile *f = input_files[i];
		uint64_t total_packets = 0, total_size = 0;

		av_log(NULL, AV_LOG_VERBOSE, "Input file #%d (%s):\n",
			i, f->ctx->filename);

		for (j = 0; j < f->nb_streams; j++) {
			InputStream *ist = input_streams[f->ist_index + j];
			enum AVMediaType type = ist->dec_ctx->codec_type;

			total_size += ist->data_size;
			total_packets += ist->nb_packets;

			av_log(NULL, AV_LOG_VERBOSE, "  Input stream #%d:%d (%s): ",
				i, j, media_type_string(type));
			av_log(NULL, AV_LOG_VERBOSE, "%I64u packets read (%I64u bytes); ",
				ist->nb_packets, ist->data_size);

			if (ist->decoding_needed) {
				av_log(NULL, AV_LOG_VERBOSE, "%I64u frames decoded",
					ist->frames_decoded);
				if (type == AVMEDIA_TYPE_AUDIO)
					av_log(NULL, AV_LOG_VERBOSE, " (%I64u samples)", ist->samples_decoded);
				av_log(NULL, AV_LOG_VERBOSE, "; ");
			}

			av_log(NULL, AV_LOG_VERBOSE, "\n");
		}

		av_log(NULL, AV_LOG_VERBOSE, "  Total: %I64u packets (%I64u bytes) demuxed\n",
			total_packets, total_size);
	}

	for (i = 0; i < nb_output_files; i++) {
		OutputFile *of = output_files[i];
		uint64_t total_packets = 0, total_size = 0;

		av_log(NULL, AV_LOG_VERBOSE, "Output file #%d (%s):\n",
			i, of->ctx->filename);

		for (j = 0; j < of->ctx->nb_streams; j++) {
			OutputStream *ost = output_streams[of->ost_index + j];
			enum AVMediaType type = ost->enc_ctx->codec_type;

			total_size += ost->data_size;
			total_packets += ost->packets_written;

			av_log(NULL, AV_LOG_VERBOSE, "  Output stream #%d:%d (%s): ",
				i, j, media_type_string(type));
			if (ost->encoding_needed) {
				av_log(NULL, AV_LOG_VERBOSE, "%I64u frames encoded",
					ost->frames_encoded);
				if (type == AVMEDIA_TYPE_AUDIO)
					av_log(NULL, AV_LOG_VERBOSE, " (%I64u samples)", ost->samples_encoded);
				av_log(NULL, AV_LOG_VERBOSE, "; ");
			}

			av_log(NULL, AV_LOG_VERBOSE, "%I64u packets muxed (%I64u bytes); ",
				ost->packets_written, ost->data_size);

			av_log(NULL, AV_LOG_VERBOSE, "\n");
		}

		av_log(NULL, AV_LOG_VERBOSE, "  Total: %I64u packets (%I64u bytes) muxed\n",
			total_packets, total_size);
	}
	if (video_size + data_size + audio_size + subtitle_size + extra_size == 0){
		av_log(NULL, AV_LOG_WARNING, "Output file is empty, nothing was encoded ");
		if (pass1_used) {
			av_log(NULL, AV_LOG_WARNING, "\n");
		}
		else {
			av_log(NULL, AV_LOG_WARNING, "(check -ss / -t / -frames parameters if used)\n");
		}
	}
}

static void print_report(int is_last_report, int64_t timer_start, int64_t cur_time)
{
	char buf[1024];
	AVBPrint buf_script;
	OutputStream *ost;
	AVFormatContext *oc;
	int64_t total_size;
	AVCodecContext *enc;
	int frame_number, vid, i;
	double bitrate;
	int64_t pts = INT64_MIN;
	static int64_t last_time = -1;
	static int qp_histogram[52];
	int hours, mins, secs, us;

	if (!print_stats && !is_last_report && !progress_avio)
		return;

	if (!is_last_report) {
		if (last_time == -1) {
			last_time = cur_time;
			return;
		}
		if ((cur_time - last_time) < 500000)
			return;
		last_time = cur_time;
	}


	oc = output_files[0]->ctx;

	total_size = avio_size(oc->pb);
	if (total_size <= 0) // FIXME improve avio_size() so it works with non seekable output too
		total_size = avio_tell(oc->pb);

	buf[0] = '\0';
	vid = 0;
	av_bprint_init(&buf_script, 0, 1);
	for (i = 0; i < nb_output_streams; i++) {
		float q = -1;
		ost = output_streams[i];
		enc = ost->enc_ctx;
		if (!ost->stream_copy)
			q = ost->quality / (float)FF_QP2LAMBDA;

		if (vid && enc->codec_type == AVMEDIA_TYPE_VIDEO) {
			_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "q=%2.1f ", q);
			av_bprintf(&buf_script, "stream_%d_%d_q=%.1f\n",
				ost->file_index, ost->index, q);
		}
		if (!vid && enc->codec_type == AVMEDIA_TYPE_VIDEO) {
			float fps, t = (cur_time - timer_start) / 1000000.0;

			frame_number = ost->frame_number;
			fps = t > 1 ? frame_number / t : 0;
			_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "frame=%5d fps=%3.*f q=%3.1f ",
				frame_number, fps < 9.95, fps, q);
			av_bprintf(&buf_script, "frame=%d\n", frame_number);
			av_bprintf(&buf_script, "fps=%.1f\n", fps);
			av_bprintf(&buf_script, "stream_%d_%d_q=%.1f\n",
				ost->file_index, ost->index, q);
			if (is_last_report)
				_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "L");
			if (qp_hist) {
				int j;
				int qp = lrintf(q);
				if (qp >= 0 && qp < FF_ARRAY_ELEMS(qp_histogram))
					qp_histogram[qp]++;
				for (j = 0; j < 32; j++)
					_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "%X", (int)lrintf(log2(float(qp_histogram[j] + 1))));
			}

			if ((enc->flags & CODEC_FLAG_PSNR) && (ost->pict_type != AV_PICTURE_TYPE_NONE || is_last_report)) {
				int j;
				double error, error_sum = 0;
				double scale, scale_sum = 0;
				double p;
				char type[3] = { 'Y', 'U', 'V' };
				_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "PSNR=");
				for (j = 0; j < 3; j++) {
					if (is_last_report) {
						error = enc->error[j];
						scale = enc->width * enc->height * 255.0 * 255.0 * frame_number;
					}
					else {
						error = ost->error[j];
						scale = enc->width * enc->height * 255.0 * 255.0;
					}
					if (j)
						scale /= 4;
					error_sum += error;
					scale_sum += scale;
					p = psnr(error / scale);
					_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "%c:%2.2f ", type[j], p);
					av_bprintf(&buf_script, "stream_%d_%d_psnr_%c=%2.2f\n",
						ost->file_index, ost->index, type[j] | 32, p);
				}
				p = psnr(error_sum / scale_sum);
				_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "*:%2.2f ", psnr(error_sum / scale_sum));
				av_bprintf(&buf_script, "stream_%d_%d_psnr_all=%2.2f\n",
					ost->file_index, ost->index, p);
			}
			vid = 1;
		}
		/* compute min output value */
		if (av_stream_get_end_pts(ost->st) != AV_NOPTS_VALUE)
			pts = FFMAX(pts, av_rescale_q(av_stream_get_end_pts(ost->st), ost->st->time_base, { 1, AV_TIME_BASE }));
		if (is_last_report)
			nb_frames_drop += ost->last_droped;
	}

	secs = FFABS(pts) / AV_TIME_BASE;
	us = FFABS(pts) % AV_TIME_BASE;
	mins = secs / 60;
	secs %= 60;
	hours = mins / 60;
	mins %= 60;

	bitrate = pts && total_size >= 0 ? total_size * 8 / (pts / 1000.0) : -1;

	if (total_size < 0) _snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf),
		"size=N/A time=");
	else                _snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf),
		"size=%8.0fkB time=", total_size / 1024.0);
	if (pts < 0)
		_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "-");
	_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf),
		"%02d:%02d:%02d.%02d ", hours, mins, secs,
		(100 * us) / AV_TIME_BASE);

	if (bitrate < 0) {
		_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "bitrate=N/A");
		av_bprintf(&buf_script, "bitrate=N/A\n");
	}
	else{
		_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), "bitrate=%6.1fkbits/s", bitrate);
		av_bprintf(&buf_script, "bitrate=%6.1fkbits/s\n", bitrate);
	}

	if (total_size < 0) av_bprintf(&buf_script, "total_size=N/A\n");
	else                av_bprintf(&buf_script, "total_size=%I64d\n", total_size);
	av_bprintf(&buf_script, "out_time_ms=%I64d\n", pts);
	av_bprintf(&buf_script, "out_time=%02d:%02d:%02d.%06d\n",
		hours, mins, secs, us);

	if (nb_frames_dup || nb_frames_drop)
		_snprintf(buf + strlen(buf), sizeof(buf)-strlen(buf), " dup=%d drop=%d",
		nb_frames_dup, nb_frames_drop);
	av_bprintf(&buf_script, "dup_frames=%d\n", nb_frames_dup);
	av_bprintf(&buf_script, "drop_frames=%d\n", nb_frames_drop);

	if (print_stats || is_last_report) {
		const char end = is_last_report ? '\n' : '\r';
		if (print_stats == 1 && AV_LOG_INFO > av_log_get_level()) {
			fprintf(stderr, "%s    %c", buf, end);
		}
		else
			av_log(NULL, AV_LOG_INFO, "%s    %c", buf, end);

		fflush(stderr);
	}

	if (progress_avio) {
		av_bprintf(&buf_script, "progress=%s\n",
			is_last_report ? "end" : "continue");
		avio_write(progress_avio, (unsigned char *)buf_script.str,
			FFMIN(buf_script.len, buf_script.size - 1));
		avio_flush(progress_avio);
		av_bprint_finalize(&buf_script, NULL);
		if (is_last_report) {
			avio_closep(&progress_avio);
		}
	}

	if (is_last_report)
		print_final_stats(total_size);
}

static void flush_encoders(void)
{
	int i, ret;

	for (i = 0; i < nb_output_streams; i++) {
		OutputStream   *ost = output_streams[i];
		AVCodecContext *enc = ost->enc_ctx;
		AVFormatContext *os = output_files[ost->file_index]->ctx;
		int stop_encoding = 0;

		if (!ost->encoding_needed)
			continue;

		if (enc->codec_type == AVMEDIA_TYPE_AUDIO && enc->frame_size <= 1)
			continue;
		if (enc->codec_type == AVMEDIA_TYPE_VIDEO && (os->oformat->flags & AVFMT_RAWPICTURE) && enc->codec->id == AV_CODEC_ID_RAWVIDEO)
			continue;

		for (;;) {
			int(*encode)(AVCodecContext*, AVPacket*, const AVFrame*, int*) = NULL;
			char *desc = "";

			switch (enc->codec_type) {
			case AVMEDIA_TYPE_AUDIO:
				encode = avcodec_encode_audio2;
				desc = "Audio";
				break;
			case AVMEDIA_TYPE_VIDEO:
				encode = avcodec_encode_video2;
				desc = "Video";
				break;
			default:
				stop_encoding = 1;
			}

			if (encode) {
				AVPacket pkt;
				int pkt_size;
				int got_packet;
				av_init_packet(&pkt);
				pkt.data = NULL;
				pkt.size = 0;

				update_benchmark(NULL);
				ret = encode(enc, &pkt, NULL, &got_packet);
				update_benchmark("flush %s %d.%d", desc, ost->file_index, ost->index);
				if (ret < 0) {
					av_log(NULL, AV_LOG_FATAL, "%s encoding failed\n", desc);
					exit_program(1);
				}
				if (ost->logfile && enc->stats_out) {
					fprintf(ost->logfile, "%s", enc->stats_out);
				}
				if (!got_packet) {
					stop_encoding = 1;
					break;
				}
				if (ost->finished & MUXER_FINISHED) {
					av_free_packet(&pkt);
					continue;
				}
				av_packet_rescale_ts(&pkt, enc->time_base, ost->st->time_base);
				pkt_size = pkt.size;
				write_frame(os, &pkt, ost);
				if (ost->enc_ctx->codec_type == AVMEDIA_TYPE_VIDEO && vstats_filename) {
					do_video_stats(ost, pkt_size);
				}
			}

			if (stop_encoding)
				break;
		}
	}
}

/*
* Check whether a packet from ist should be written into ost at this time
*/
static int check_output_constraints(InputStream *ist, OutputStream *ost)
{
	OutputFile *of = output_files[ost->file_index];
	int ist_index = input_files[ist->file_index]->ist_index + ist->st->index;

	if (ost->source_index != ist_index)
		return 0;

	if (ost->finished)
		return 0;

	if (of->start_time != AV_NOPTS_VALUE && ist->pts < of->start_time)
		return 0;

	return 1;
}

static void do_streamcopy(InputStream *ist, OutputStream *ost, const AVPacket *pkt)
{
	OutputFile *of = output_files[ost->file_index];
	InputFile   *f = input_files[ist->file_index];
	int64_t start_time = (of->start_time == AV_NOPTS_VALUE) ? 0 : of->start_time;
	int64_t ost_tb_start_time = av_rescale_q(start_time, { 1, AV_TIME_BASE }, ost->st->time_base);
	int64_t ist_tb_start_time = av_rescale_q(start_time, { 1, AV_TIME_BASE }, ist->st->time_base);
	AVPicture pict;
	AVPacket opkt;

	av_init_packet(&opkt);

	if ((!ost->frame_number && !(pkt->flags & AV_PKT_FLAG_KEY)) &&
		!ost->copy_initial_nonkeyframes)
		return;

	if (pkt->pts == AV_NOPTS_VALUE) {
		if (!ost->frame_number && ist->pts < start_time &&
			!ost->copy_prior_start)
			return;
	}
	else {
		if (!ost->frame_number && pkt->pts < ist_tb_start_time &&
			!ost->copy_prior_start)
			return;
	}

	if (of->recording_time != INT64_MAX &&
		ist->pts >= of->recording_time + start_time) {
		close_output_stream(ost);
		return;
	}

	if (f->recording_time != INT64_MAX) {
		start_time = f->ctx->start_time;
		if (f->start_time != AV_NOPTS_VALUE)
			start_time += f->start_time;
		if (ist->pts >= f->recording_time + start_time) {
			close_output_stream(ost);
			return;
		}
	}

	/* force the input stream PTS */
	if (ost->enc_ctx->codec_type == AVMEDIA_TYPE_VIDEO)
		ost->sync_opts++;

	if (pkt->pts != AV_NOPTS_VALUE)
		opkt.pts = av_rescale_q(pkt->pts, ist->st->time_base, ost->st->time_base) - ost_tb_start_time;
	else
		opkt.pts = AV_NOPTS_VALUE;

	if (pkt->dts == AV_NOPTS_VALUE)
		opkt.dts = av_rescale_q(ist->dts, { 1, AV_TIME_BASE }, ost->st->time_base);
	else
		opkt.dts = av_rescale_q(pkt->dts, ist->st->time_base, ost->st->time_base);
	opkt.dts -= ost_tb_start_time;

	if (ost->st->codec->codec_type == AVMEDIA_TYPE_AUDIO && pkt->dts != AV_NOPTS_VALUE) {
		int duration = av_get_audio_frame_duration(ist->dec_ctx, pkt->size);
		if (!duration)
			duration = ist->dec_ctx->frame_size;
		opkt.dts = opkt.pts = av_rescale_delta(ist->st->time_base, pkt->dts,
		{ 1, ist->dec_ctx->sample_rate }, duration, &ist->filter_in_rescale_delta_last,
		ost->st->time_base) - ost_tb_start_time;
	}

	opkt.duration = av_rescale_q(pkt->duration, ist->st->time_base, ost->st->time_base);
	opkt.flags = pkt->flags;

	// FIXME remove the following 2 lines they shall be replaced by the bitstream filters
	if (ost->enc_ctx->codec_id != AV_CODEC_ID_H264
		&& ost->enc_ctx->codec_id != AV_CODEC_ID_MPEG1VIDEO
		&& ost->enc_ctx->codec_id != AV_CODEC_ID_MPEG2VIDEO
		&& ost->enc_ctx->codec_id != AV_CODEC_ID_VC1
		) {
		if (av_parser_change(ost->parser, ost->st->codec,
			&opkt.data, &opkt.size,
			pkt->data, pkt->size,
			pkt->flags & AV_PKT_FLAG_KEY)) {
			opkt.buf = av_buffer_create(opkt.data, opkt.size, av_buffer_default_free, NULL, 0);
			if (!opkt.buf)
				exit_program(1);
		}
	}
	else {
		opkt.data = pkt->data;
		opkt.size = pkt->size;
	}
	av_copy_packet_side_data(&opkt, pkt);

	if (ost->st->codec->codec_type == AVMEDIA_TYPE_VIDEO && (of->ctx->oformat->flags & AVFMT_RAWPICTURE)) {
		/* store AVPicture in AVPacket, as expected by the output format */
		avpicture_fill(&pict, opkt.data, ost->st->codec->pix_fmt, ost->st->codec->width, ost->st->codec->height);
		opkt.data = (uint8_t *)&pict;
		opkt.size = sizeof(AVPicture);
		opkt.flags |= AV_PKT_FLAG_KEY;
	}

	write_frame(of->ctx, &opkt, ost);
}

int guess_input_channel_layout(InputStream *ist)
{
	AVCodecContext *dec = ist->dec_ctx;

	if (!dec->channel_layout) {
		char layout_name[256];

		if (dec->channels > ist->guess_layout_max)
			return 0;
		dec->channel_layout = av_get_default_channel_layout(dec->channels);
		if (!dec->channel_layout)
			return 0;
		av_get_channel_layout_string(layout_name, sizeof(layout_name),
			dec->channels, dec->channel_layout);
		av_log(NULL, AV_LOG_WARNING, "Guessed Channel Layout for  Input Stream "
			"#%d.%d : %s\n", ist->file_index, ist->st->index, layout_name);
	}
	return 1;
}

static int decode_audio(InputStream *ist, AVPacket *pkt, int *got_output)
{
	AVFrame *decoded_frame, *f;
	AVCodecContext *avctx = ist->dec_ctx;
	int i, ret, err = 0, resample_changed;
	AVRational decoded_frame_tb;

	if (!ist->decoded_frame && !(ist->decoded_frame = av_frame_alloc()))
		return AVERROR(ENOMEM);
	if (!ist->filter_frame && !(ist->filter_frame = av_frame_alloc()))
		return AVERROR(ENOMEM);
	decoded_frame = ist->decoded_frame;

	update_benchmark(NULL);
	ret = avcodec_decode_audio4(avctx, decoded_frame, got_output, pkt);
	update_benchmark("decode_audio %d.%d", ist->file_index, ist->st->index);

	if (ret >= 0 && avctx->sample_rate <= 0) {
		av_log(avctx, AV_LOG_ERROR, "Sample rate %d invalid\n", avctx->sample_rate);
		ret = AVERROR_INVALIDDATA;
	}

	if (*got_output || ret<0)
		decode_error_stat[ret<0] ++;

	if (ret < 0 && exit_on_error)
		exit_program(1);

	if (!*got_output || ret < 0)
		return ret;

	ist->samples_decoded += decoded_frame->nb_samples;
	ist->frames_decoded++;

#if 1
	/* increment next_dts to use for the case where the input stream does not
	have timestamps or there are multiple frames in the packet */
	ist->next_pts += ((int64_t)AV_TIME_BASE * decoded_frame->nb_samples) /
		avctx->sample_rate;
	ist->next_dts += ((int64_t)AV_TIME_BASE * decoded_frame->nb_samples) /
		avctx->sample_rate;
#endif

	resample_changed = ist->resample_sample_fmt != decoded_frame->format ||
		ist->resample_channels != avctx->channels ||
		ist->resample_channel_layout != decoded_frame->channel_layout ||
		ist->resample_sample_rate != decoded_frame->sample_rate;
	if (resample_changed) {
		char layout1[64], layout2[64];

		if (!guess_input_channel_layout(ist)) {
			av_log(NULL, AV_LOG_FATAL, "Unable to find default channel "
				"layout for Input Stream #%d.%d\n", ist->file_index,
				ist->st->index);
			exit_program(1);
		}
		decoded_frame->channel_layout = avctx->channel_layout;

		av_get_channel_layout_string(layout1, sizeof(layout1), ist->resample_channels,
			ist->resample_channel_layout);
		av_get_channel_layout_string(layout2, sizeof(layout2), avctx->channels,
			decoded_frame->channel_layout);

		av_log(NULL, AV_LOG_INFO,
			"Input stream #%d:%d frame changed from rate:%d fmt:%s ch:%d chl:%s to rate:%d fmt:%s ch:%d chl:%s\n",
			ist->file_index, ist->st->index,
			ist->resample_sample_rate, av_get_sample_fmt_name((AVSampleFormat)ist->resample_sample_fmt),
			ist->resample_channels, layout1,
			decoded_frame->sample_rate, av_get_sample_fmt_name((AVSampleFormat)decoded_frame->format),
			avctx->channels, layout2);

		ist->resample_sample_fmt = decoded_frame->format;
		ist->resample_sample_rate = decoded_frame->sample_rate;
		ist->resample_channel_layout = decoded_frame->channel_layout;
		ist->resample_channels = avctx->channels;

		for (i = 0; i < nb_filtergraphs; i++)
		if (ist_in_filtergraph(filtergraphs[i], ist)) {
			FilterGraph *fg = filtergraphs[i];
			if (configure_filtergraph(fg) < 0) {
				av_log(NULL, AV_LOG_FATAL, "Error reinitializing filters!\n");
				exit_program(1);
			}
		}
	}

	/* if the decoder provides a pts, use it instead of the last packet pts.
	the decoder could be delaying output by a packet or more. */
	if (decoded_frame->pts != AV_NOPTS_VALUE) {
		ist->dts = ist->next_dts = ist->pts = ist->next_pts = av_rescale_q(decoded_frame->pts, avctx->time_base, { 1, AV_TIME_BASE });
		decoded_frame_tb = avctx->time_base;
	}
	else if (decoded_frame->pkt_pts != AV_NOPTS_VALUE) {
		decoded_frame->pts = decoded_frame->pkt_pts;
		decoded_frame_tb = ist->st->time_base;
	}
	else if (pkt->pts != AV_NOPTS_VALUE) {
		decoded_frame->pts = pkt->pts;
		decoded_frame_tb = ist->st->time_base;
	}
	else {
		decoded_frame->pts = ist->dts;
		decoded_frame_tb = { 1, AV_TIME_BASE };
	}
	pkt->pts = AV_NOPTS_VALUE;
	if (decoded_frame->pts != AV_NOPTS_VALUE)
		decoded_frame->pts = av_rescale_delta(decoded_frame_tb, decoded_frame->pts,
		{ 1, avctx->sample_rate }, decoded_frame->nb_samples, &ist->filter_in_rescale_delta_last,
		{ 1, avctx->sample_rate });
	for (i = 0; i < ist->nb_filters; i++) {
		if (i < ist->nb_filters - 1) {
			f = ist->filter_frame;
			err = av_frame_ref(f, decoded_frame);
			if (err < 0)
				break;
		}
		else
			f = decoded_frame;
		err = av_buffersrc_add_frame_flags(ist->filters[i]->filter, f,
			AV_BUFFERSRC_FLAG_PUSH);
		if (err == AVERROR_EOF)
			err = 0; /* ignore */
		if (err < 0)
			break;
	}
	decoded_frame->pts = AV_NOPTS_VALUE;

	av_frame_unref(ist->filter_frame);
	av_frame_unref(decoded_frame);
	return err < 0 ? err : ret;
}

static int decode_video(InputStream *ist, AVPacket *pkt, int *got_output)
{
	AVFrame *decoded_frame, *f;
	int i, ret = 0, err = 0, resample_changed;
	int64_t best_effort_timestamp;
	AVRational *frame_sample_aspect;

	if (!ist->decoded_frame && !(ist->decoded_frame = av_frame_alloc()))
		return AVERROR(ENOMEM);
	if (!ist->filter_frame && !(ist->filter_frame = av_frame_alloc()))
		return AVERROR(ENOMEM);
	decoded_frame = ist->decoded_frame;
	pkt->dts = av_rescale_q(ist->dts, { 1, AV_TIME_BASE }, ist->st->time_base);

	update_benchmark(NULL);

	ret = avcodec_decode_video2(ist->dec_ctx,
		decoded_frame, got_output, pkt);
	update_benchmark("decode_video %d.%d", ist->file_index, ist->st->index);

	// The following line may be required in some cases where there is no parser
	// or the parser does not has_b_frames correctly
	if (ist->st->codec->has_b_frames < ist->dec_ctx->has_b_frames) {
		if (ist->dec_ctx->codec_id == AV_CODEC_ID_H264) {
			ist->st->codec->has_b_frames = ist->dec_ctx->has_b_frames;
		}
	}

	if (*got_output || ret<0)
		decode_error_stat[ret<0] ++;

	if (ret < 0 && exit_on_error)
		exit_program(1);

	if (*got_output && ret >= 0) {
		if (ist->dec_ctx->width != decoded_frame->width ||
			ist->dec_ctx->height != decoded_frame->height ||
			ist->dec_ctx->pix_fmt != decoded_frame->format) {
			av_log(NULL, AV_LOG_DEBUG, "Frame parameters mismatch context %d,%d,%d != %d,%d,%d\n",
				decoded_frame->width,
				decoded_frame->height,
				decoded_frame->format,
				ist->dec_ctx->width,
				ist->dec_ctx->height,
				ist->dec_ctx->pix_fmt);
		}
	}

	if (!*got_output || ret < 0)
		return ret;

	if (ist->top_field_first >= 0)
		decoded_frame->top_field_first = ist->top_field_first;

	ist->frames_decoded++;

	if (ist->hwaccel_retrieve_data && decoded_frame->format == ist->hwaccel_pix_fmt) {
		err = ist->hwaccel_retrieve_data(ist->dec_ctx, decoded_frame);
		if (err < 0)
			goto fail;
	}
	ist->hwaccel_retrieved_pix_fmt = (AVPixelFormat)decoded_frame->format;

	best_effort_timestamp = av_frame_get_best_effort_timestamp(decoded_frame);
	if (best_effort_timestamp != AV_NOPTS_VALUE)
		ist->next_pts = ist->pts = av_rescale_q(decoded_frame->pts = best_effort_timestamp, ist->st->time_base, { 1, AV_TIME_BASE });

	if (debug_ts) {
		av_log(NULL, AV_LOG_INFO, "decoder -> ist_index:%d type:video "
			"frame_pts:%s frame_pts_time:%s best_effort_ts:%I64d best_effort_ts_time:%s keyframe:%d frame_type:%d time_base:%d/%d\n",
			ist->st->index, av_ts2str(decoded_frame->pts),
			av_ts2timestr(decoded_frame->pts, &ist->st->time_base),
			best_effort_timestamp,
			av_ts2timestr(best_effort_timestamp, &ist->st->time_base),
			decoded_frame->key_frame, decoded_frame->pict_type,
			ist->st->time_base.num, ist->st->time_base.den);
	}

	pkt->size = 0;

	if (ist->st->sample_aspect_ratio.num)
		decoded_frame->sample_aspect_ratio = ist->st->sample_aspect_ratio;

	resample_changed = ist->resample_width != decoded_frame->width ||
		ist->resample_height != decoded_frame->height ||
		ist->resample_pix_fmt != decoded_frame->format;
	if (resample_changed) {
		av_log(NULL, AV_LOG_INFO,
			"Input stream #%d:%d frame changed from size:%dx%d fmt:%s to size:%dx%d fmt:%s\n",
			ist->file_index, ist->st->index,
			ist->resample_width, ist->resample_height, av_get_pix_fmt_name((AVPixelFormat)ist->resample_pix_fmt),
			decoded_frame->width, decoded_frame->height, av_get_pix_fmt_name((AVPixelFormat)decoded_frame->format));

		ist->resample_width = decoded_frame->width;
		ist->resample_height = decoded_frame->height;
		ist->resample_pix_fmt = decoded_frame->format;

		for (i = 0; i < nb_filtergraphs; i++) {
			if (ist_in_filtergraph(filtergraphs[i], ist) && ist->reinit_filters &&
				configure_filtergraph(filtergraphs[i]) < 0) {
				av_log(NULL, AV_LOG_FATAL, "Error reinitializing filters!\n");
				exit_program(1);
			}
		}
	}

	frame_sample_aspect = (AVRational *)av_opt_ptr(avcodec_get_frame_class(), decoded_frame, "sample_aspect_ratio");
	for (i = 0; i < ist->nb_filters; i++) {
		if (!frame_sample_aspect->num)
			*frame_sample_aspect = ist->st->sample_aspect_ratio;

		if (i < ist->nb_filters - 1) {
			f = ist->filter_frame;
			err = av_frame_ref(f, decoded_frame);
			if (err < 0)
				break;
		}
		else
			f = decoded_frame;
		ret = av_buffersrc_add_frame_flags(ist->filters[i]->filter, f, AV_BUFFERSRC_FLAG_PUSH);
		if (ret == AVERROR_EOF) {
			ret = 0; /* ignore */
		}
		else if (ret < 0) {
			av_log(NULL, AV_LOG_FATAL,
				"Failed to inject frame into filter network: %s\n", av_err2str(ret));
			exit_program(1);
		}
	}

fail:
	av_frame_unref(ist->filter_frame);
	av_frame_unref(decoded_frame);
	return err < 0 ? err : ret;
}

static int transcode_subtitles(InputStream *ist, AVPacket *pkt, int *got_output)
{
	AVSubtitle subtitle;
	int i, ret = avcodec_decode_subtitle2(ist->dec_ctx,
		&subtitle, got_output, pkt);

	if (*got_output || ret<0)
		decode_error_stat[ret<0] ++;

	if (ret < 0 && exit_on_error)
		exit_program(1);

	if (ret < 0 || !*got_output) {
		if (!pkt->size)
			sub2video_flush(ist);
		return ret;
	}

	if (ist->fix_sub_duration) {
		int end = 1;
		if (ist->prev_sub.got_output) {
			end = av_rescale(subtitle.pts - ist->prev_sub.subtitle.pts,
				1000, AV_TIME_BASE);
			if (end < ist->prev_sub.subtitle.end_display_time) {
				av_log(ist->dec_ctx, AV_LOG_DEBUG,
					"Subtitle duration reduced from %d to %d%s\n",
					ist->prev_sub.subtitle.end_display_time, end,
					end <= 0 ? ", dropping it" : "");
				ist->prev_sub.subtitle.end_display_time = end;
			}
		}
		FFSWAP(int, *got_output, ist->prev_sub.got_output);
		FFSWAP(int, ret, ist->prev_sub.ret);
		FFSWAP(AVSubtitle, subtitle, ist->prev_sub.subtitle);
		if (end <= 0)
			goto out;
	}

	if (!*got_output)
		return ret;

	sub2video_update(ist, &subtitle);

	if (!subtitle.num_rects)
		goto out;

	ist->frames_decoded++;

	for (i = 0; i < nb_output_streams; i++) {
		OutputStream *ost = output_streams[i];

		if (!check_output_constraints(ist, ost) || !ost->encoding_needed
			|| ost->enc->type != AVMEDIA_TYPE_SUBTITLE)
			continue;

		do_subtitle_out(output_files[ost->file_index]->ctx, ost, ist, &subtitle);
	}

out:
	avsubtitle_free(&subtitle);
	return ret;
}

static int send_filter_eof(InputStream *ist)
{
	int i, ret;
	for (i = 0; i < ist->nb_filters; i++) {
#if 1
		ret = av_buffersrc_add_ref(ist->filters[i]->filter, NULL, 0);
#else
		ret = av_buffersrc_add_frame(ist->filters[i]->filter, NULL);
#endif
		if (ret < 0)
			return ret;
	}
	return 0;
}

/* pkt = NULL means EOF (needed to flush decoder buffers) */
static int process_input_packet(InputStream *ist, const AVPacket *pkt)
{
	int ret = 0, i;
	int got_output = 0;

	AVPacket avpkt;
	if (!ist->saw_first_ts) {
		ist->dts = ist->st->avg_frame_rate.num ? -ist->dec_ctx->has_b_frames * AV_TIME_BASE / av_q2d(ist->st->avg_frame_rate) : 0;
		ist->pts = 0;
		if (pkt && pkt->pts != AV_NOPTS_VALUE && !ist->decoding_needed) {
			ist->dts += av_rescale_q(pkt->pts, ist->st->time_base, { 1, AV_TIME_BASE });
			ist->pts = ist->dts; //unused but better to set it to a value thats not totally wrong
		}
		ist->saw_first_ts = 1;
	}

	if (ist->next_dts == AV_NOPTS_VALUE)
		ist->next_dts = ist->dts;
	if (ist->next_pts == AV_NOPTS_VALUE)
		ist->next_pts = ist->pts;

	if (!pkt) {
		/* EOF handling */
		av_init_packet(&avpkt);
		avpkt.data = NULL;
		avpkt.size = 0;
		goto handle_eof;
	}
	else {
		avpkt = *pkt;
	}

	if (pkt->dts != AV_NOPTS_VALUE) {
		ist->next_dts = ist->dts = av_rescale_q(pkt->dts, ist->st->time_base, { 1, AV_TIME_BASE });
		if (ist->dec_ctx->codec_type != AVMEDIA_TYPE_VIDEO || !ist->decoding_needed)
			ist->next_pts = ist->pts = ist->dts;
	}

	// while we have more to decode or while the decoder did output something on EOF
	while (ist->decoding_needed && (avpkt.size > 0 || (!pkt && got_output))) {
		int duration;
	handle_eof:

		ist->pts = ist->next_pts;
		ist->dts = ist->next_dts;

		if (avpkt.size && avpkt.size != pkt->size &&
			!(ist->dec->capabilities & CODEC_CAP_SUBFRAMES)) {
			av_log(NULL, ist->showed_multi_packet_warning ? AV_LOG_VERBOSE : AV_LOG_WARNING,
				"Multiple frames in a packet from stream %d\n", pkt->stream_index);
			ist->showed_multi_packet_warning = 1;
		}

		switch (ist->dec_ctx->codec_type) {
		case AVMEDIA_TYPE_AUDIO:
			ret = decode_audio(ist, &avpkt, &got_output);
			break;
		case AVMEDIA_TYPE_VIDEO:
			//zhangnh = zhangnh + 1;
			ret = decode_video(ist, &avpkt, &got_output);
			if (avpkt.duration) {
				duration = av_rescale_q(avpkt.duration, ist->st->time_base, { 1, AV_TIME_BASE });
			}
			else if (ist->dec_ctx->framerate.num != 0 && ist->dec_ctx->framerate.den != 0) {
				int ticks = av_stream_get_parser(ist->st) ? av_stream_get_parser(ist->st)->repeat_pict + 1 : ist->dec_ctx->ticks_per_frame;
				duration = ((int64_t)AV_TIME_BASE *
					ist->dec_ctx->framerate.den * ticks) /
					ist->dec_ctx->framerate.num / ist->dec_ctx->ticks_per_frame;
			}
			else
				duration = 0;

			if (ist->dts != AV_NOPTS_VALUE && duration) {
				ist->next_dts += duration;
			}
			else
				ist->next_dts = AV_NOPTS_VALUE;

			if (got_output)
				ist->next_pts += duration; //FIXME the duration is not correct in some cases
			break;
		case AVMEDIA_TYPE_SUBTITLE:
			ret = transcode_subtitles(ist, &avpkt, &got_output);
			break;
		default:
			return -1;
		}

		if (ret < 0) {
			av_log(NULL, AV_LOG_ERROR, "Error while decoding stream #%d:%d: %s\n",
				ist->file_index, ist->st->index, av_err2str(ret));
			if (exit_on_error)
				exit_program(1);
			break;
		}

		avpkt.dts =
			avpkt.pts = AV_NOPTS_VALUE;

		// touch data and size only if not EOF
		if (pkt) {
			if (ist->dec_ctx->codec_type != AVMEDIA_TYPE_AUDIO)
				ret = avpkt.size;
			avpkt.data += ret;
			avpkt.size -= ret;
		}
		if (!got_output) {
			continue;
		}
		if (got_output && !pkt)
			break;
	}

	/* after flushing, send an EOF on all the filter inputs attached to the stream */
	if (!pkt && ist->decoding_needed && !got_output) {
		int ret = send_filter_eof(ist);
		if (ret < 0) {
			av_log(NULL, AV_LOG_FATAL, "Error marking filters as finished\n");
			exit_program(1);
		}
	}

	/* handle stream copy */
	if (!ist->decoding_needed) {
		ist->dts = ist->next_dts;
		switch (ist->dec_ctx->codec_type) {
		case AVMEDIA_TYPE_AUDIO:
			ist->next_dts += ((int64_t)AV_TIME_BASE * ist->dec_ctx->frame_size) /
				ist->dec_ctx->sample_rate;
			break;
		case AVMEDIA_TYPE_VIDEO:
			if (ist->framerate.num) {
				// TODO: Remove work-around for c99-to-c89 issue 7
				AVRational time_base_q = { 1, AV_TIME_BASE };
				int64_t next_dts = av_rescale_q(ist->next_dts, time_base_q, av_inv_q(ist->framerate));
				ist->next_dts = av_rescale_q(next_dts + 1, av_inv_q(ist->framerate), time_base_q);
			}
			else if (pkt->duration) {
				ist->next_dts += av_rescale_q(pkt->duration, ist->st->time_base, { 1, AV_TIME_BASE });
			}
			else if (ist->dec_ctx->framerate.num != 0) {
				int ticks = av_stream_get_parser(ist->st) ? av_stream_get_parser(ist->st)->repeat_pict + 1 : ist->dec_ctx->ticks_per_frame;
				ist->next_dts += ((int64_t)AV_TIME_BASE *
					ist->dec_ctx->framerate.den * ticks) /
					ist->dec_ctx->framerate.num / ist->dec_ctx->ticks_per_frame;
			}
			break;
		}
		ist->pts = ist->dts;
		ist->next_pts = ist->next_dts;
	}
	for (i = 0; pkt && i < nb_output_streams; i++) {
		OutputStream *ost = output_streams[i];

		if (!check_output_constraints(ist, ost) || ost->encoding_needed)
			continue;

		do_streamcopy(ist, ost, pkt);
	}

	return got_output;
}

static void print_sdp(void)
{
	char sdp[16384];
	int i;
	int j;
	AVIOContext *sdp_pb;
	AVFormatContext **avc = (AVFormatContext **)av_malloc_array(nb_output_files, sizeof(*avc));

	if (!avc)
		exit_program(1);
	for (i = 0, j = 0; i < nb_output_files; i++) {
		if (!strcmp(output_files[i]->ctx->oformat->name, "rtp")) {
			avc[j] = output_files[i]->ctx;
			j++;
		}
	}

	av_sdp_create(avc, j, sdp, sizeof(sdp));

	if (!sdp_filename) {
		printf("SDP:\n%s\n", sdp);
		fflush(stdout);
	}
	else {
		if (avio_open2(&sdp_pb, sdp_filename, AVIO_FLAG_WRITE, &int_cb, NULL) < 0) {
			av_log(NULL, AV_LOG_ERROR, "Failed to open sdp file '%s'\n", sdp_filename);
		}
		else {
			avio_printf(sdp_pb, "SDP:\n%s", sdp);
			avio_closep(&sdp_pb);
			av_freep(&sdp_filename);
		}
	}

	av_freep(&avc);
}

static const HWAccel *get_hwaccel(enum AVPixelFormat pix_fmt)
{
	int i;
	for (i = 0; hwaccels[i].name; i++)
	if (hwaccels[i].pix_fmt == pix_fmt)
		return &hwaccels[i];
	return NULL;
}

static enum AVPixelFormat get_format(AVCodecContext *s, const enum AVPixelFormat *pix_fmts)
{
	InputStream *ist = (InputStream *)s->opaque;
	const enum AVPixelFormat *p;
	int ret;

	for (p = pix_fmts; *p != -1; p++) {
		const AVPixFmtDescriptor *desc = av_pix_fmt_desc_get(*p);
		const HWAccel *hwaccel;

		if (!(desc->flags & AV_PIX_FMT_FLAG_HWACCEL))
			break;

		hwaccel = get_hwaccel(*p);
		if (!hwaccel ||
			(ist->active_hwaccel_id && ist->active_hwaccel_id != hwaccel->id) ||
			(ist->hwaccel_id != HWACCEL_AUTO && ist->hwaccel_id != hwaccel->id))
			continue;

		ret = hwaccel->init(s);
		if (ret < 0) {
			if (ist->hwaccel_id == hwaccel->id) {
				av_log(NULL, AV_LOG_FATAL,
					"%s hwaccel requested for input stream #%d:%d, "
					"but cannot be initialized.\n", hwaccel->name,
					ist->file_index, ist->st->index);
				return AV_PIX_FMT_NONE;
			}
			continue;
		}
		ist->active_hwaccel_id = hwaccel->id;
		ist->hwaccel_pix_fmt = *p;
		break;
	}

	return *p;
}

static int get_buffer(AVCodecContext *s, AVFrame *frame, int flags)
{
	InputStream *ist = (InputStream *)s->opaque;

	if (ist->hwaccel_get_buffer && frame->format == ist->hwaccel_pix_fmt)
		return ist->hwaccel_get_buffer(s, frame, flags);

	return avcodec_default_get_buffer2(s, frame, flags);
}

static int init_input_stream(int ist_index, char *error, int error_len)
{
	int ret;
	InputStream *ist = input_streams[ist_index];

	if (ist->decoding_needed) {
		AVCodec *codec = ist->dec;
		if (!codec) {
			_snprintf(error, error_len, "Decoder (codec %s) not found for input stream #%d:%d",
				avcodec_get_name(ist->dec_ctx->codec_id), ist->file_index, ist->st->index);
			return AVERROR(EINVAL);
		}

		ist->dec_ctx->opaque = ist;
		ist->dec_ctx->get_format = get_format;
		ist->dec_ctx->get_buffer2 = get_buffer;
		ist->dec_ctx->thread_safe_callbacks = 1;

		av_opt_set_int(ist->dec_ctx, "refcounted_frames", 1, 0);
		if (ist->dec_ctx->codec_id == AV_CODEC_ID_DVB_SUBTITLE &&
			(ist->decoding_needed & DECODING_FOR_OST)) {
			av_dict_set(&ist->decoder_opts, "compute_edt", "1", AV_DICT_DONT_OVERWRITE);
			if (ist->decoding_needed & DECODING_FOR_FILTER)
				av_log(NULL, AV_LOG_WARNING, "Warning using DVB subtitles for filtering and output at the same time is not fully supported, also see -compute_edt [0|1]\n");
		}

		if (!av_dict_get(ist->decoder_opts, "threads", NULL, 0))
			av_dict_set(&ist->decoder_opts, "threads", "auto", 0);
		if ((ret = avcodec_open2(ist->dec_ctx, codec, &ist->decoder_opts)) < 0) {  //打开解码器
			if (ret == AVERROR_EXPERIMENTAL)
				abort_codec_experimental(codec, 0);

			_snprintf(error, error_len,
				"Error while opening decoder for input stream "
				"#%d:%d : %s",
				ist->file_index, ist->st->index, av_err2str(ret));
			return ret;
		}
		assert_avoptions(ist->decoder_opts);
	}

	ist->next_pts = AV_NOPTS_VALUE;
	ist->next_dts = AV_NOPTS_VALUE;

	return 0;
}

static InputStream *get_input_stream(OutputStream *ost)
{
	if (ost->source_index >= 0)
		return input_streams[ost->source_index];
	return NULL;
}

static int compare_int64(const void *a, const void *b)
{
	int64_t va = *(int64_t *)a, vb = *(int64_t *)b;
	return va < vb ? -1 : va > vb ? +1 : 0;
}

static int init_output_stream(OutputStream *ost, char *error, int error_len)
{
	int ret = 0;

	if (ost->encoding_needed) {
		AVCodec      *codec = ost->enc;
		AVCodecContext *dec = NULL;
		InputStream *ist;

		if ((ist = get_input_stream(ost)))
			dec = ist->dec_ctx;
		if (dec && dec->subtitle_header) {
			/* ASS code assumes this buffer is null terminated so add extra byte. */
			ost->enc_ctx->subtitle_header = (uint8_t *)av_mallocz(dec->subtitle_header_size + 1);
			if (!ost->enc_ctx->subtitle_header)
				return AVERROR(ENOMEM);
			memcpy(ost->enc_ctx->subtitle_header, dec->subtitle_header, dec->subtitle_header_size);
			ost->enc_ctx->subtitle_header_size = dec->subtitle_header_size;
		}
		if (!av_dict_get(ost->encoder_opts, "threads", NULL, 0))
			av_dict_set(&ost->encoder_opts, "threads", "auto", 0);
		av_dict_set(&ost->encoder_opts, "side_data_only_packets", "1", 0);

		if ((ret = avcodec_open2(ost->enc_ctx, codec, &ost->encoder_opts)) < 0) {
			if (ret == AVERROR_EXPERIMENTAL)
				abort_codec_experimental(codec, 1);
			_snprintf(error, error_len,
				"Error while opening encoder for output stream #%d:%d - "
				"maybe incorrect parameters such as bit_rate, rate, width or height",
				ost->file_index, ost->index);
			return ret;
		}
		if (ost->enc->type == AVMEDIA_TYPE_AUDIO &&
			!(ost->enc->capabilities & CODEC_CAP_VARIABLE_FRAME_SIZE))
			av_buffersink_set_frame_size(ost->filter->filter,
			ost->enc_ctx->frame_size);
		assert_avoptions(ost->encoder_opts);
		if (ost->enc_ctx->bit_rate && ost->enc_ctx->bit_rate < 1000)
			av_log(NULL, AV_LOG_WARNING, "The bitrate parameter is set too low."
			" It takes bits/s as argument, not kbits/s\n");

		ret = avcodec_copy_context(ost->st->codec, ost->enc_ctx);
		if (ret < 0) {
			av_log(NULL, AV_LOG_FATAL,
				"Error initializing the output stream codec context.\n");
			exit_program(1);
		}

		// copy timebase while removing common factors
		ost->st->time_base = av_add_q(ost->enc_ctx->time_base, { 0, 1 });
		ost->st->codec->codec = ost->enc_ctx->codec;
	}
	else {
		ret = av_opt_set_dict(ost->enc_ctx, &ost->encoder_opts);
		if (ret < 0) {
			av_log(NULL, AV_LOG_FATAL,
				"Error setting up codec context options.\n");
			return ret;
		}
		// copy timebase while removing common factors
		ost->st->time_base = av_add_q(ost->st->codec->time_base, { 0, 1 });
	}

	return ret;
}

static void parse_forced_key_frames(char *kf, OutputStream *ost,
	AVCodecContext *avctx)
{
	char *p;
	int n = 1, i, size, index = 0;
	int64_t t, *pts;

	for (p = kf; *p; p++)
	if (*p == ',')
		n++;
	size = n;
	pts = (int64_t*)av_malloc_array(size, sizeof(*pts));
	if (!pts) {
		av_log(NULL, AV_LOG_FATAL, "Could not allocate forced key frames array.\n");
		exit_program(1);
	}

	p = kf;
	for (i = 0; i < n; i++) {
		char *next = strchr(p, ',');

		if (next)
			*next++ = 0;

		if (!memcmp(p, "chapters", 8)) {

			AVFormatContext *avf = output_files[ost->file_index]->ctx;
			int j;

			if (avf->nb_chapters > INT_MAX - size ||
				!(pts = (int64_t*)av_realloc_f(pts, size += avf->nb_chapters - 1,
				sizeof(*pts)))) {
				av_log(NULL, AV_LOG_FATAL,
					"Could not allocate forced key frames array.\n");
				exit_program(1);
			}
			t = p[8] ? parse_time_or_die("force_key_frames", p + 8, 1) : 0;
			t = av_rescale_q(t, { 1, AV_TIME_BASE }, avctx->time_base);

			for (j = 0; j < avf->nb_chapters; j++) {
				AVChapter *c = avf->chapters[j];
				av_assert1(index < size);
				pts[index++] = av_rescale_q(c->start, c->time_base,
					avctx->time_base) + t;
			}

		}
		else {

			t = parse_time_or_die("force_key_frames", p, 1);
			av_assert1(index < size);
			pts[index++] = av_rescale_q(t, { 1, AV_TIME_BASE }, avctx->time_base);

		}

		p = next;
	}

	av_assert0(index == size);
	qsort(pts, size, sizeof(*pts), compare_int64);
	ost->forced_kf_count = size;
	ost->forced_kf_pts = pts;
}

static void report_new_stream(int input_index, AVPacket *pkt)
{
	InputFile *file = input_files[input_index];
	AVStream *st = file->ctx->streams[pkt->stream_index];

	if (pkt->stream_index < file->nb_streams_warn)
		return;
	av_log(file->ctx, AV_LOG_WARNING,
		"New %s stream %d:%d at pos:%I64d and DTS:%ss\n",
		av_get_media_type_string(st->codec->codec_type),
		input_index, pkt->stream_index,
		pkt->pos, av_ts2timestr(pkt->dts, &st->time_base));
	file->nb_streams_warn = pkt->stream_index + 1;
}

static void set_encoder_id(OutputFile *of, OutputStream *ost)
{
	AVDictionaryEntry *e;

	uint8_t *encoder_string;
	int encoder_string_len;
	int format_flags = 0;
	int codec_flags = 0;

	if (av_dict_get(ost->st->metadata, "encoder", NULL, 0))
		return;

	e = av_dict_get(of->opts, "fflags", NULL, 0);
	if (e) {
		const AVOption *o = av_opt_find(of->ctx, "fflags", NULL, 0, 0);
		if (!o)
			return;
		av_opt_eval_flags(of->ctx, o, e->value, &format_flags);
	}
	e = av_dict_get(ost->encoder_opts, "flags", NULL, 0);
	if (e) {
		const AVOption *o = av_opt_find(ost->enc_ctx, "flags", NULL, 0, 0);
		if (!o)
			return;
		av_opt_eval_flags(ost->enc_ctx, o, e->value, &codec_flags);
	}

	encoder_string_len = sizeof(LIBAVCODEC_IDENT)+strlen(ost->enc->name) + 2;
	encoder_string = (uint8_t *)av_mallocz(encoder_string_len);
	if (!encoder_string)
		exit_program(1);

	if (!(format_flags & AVFMT_FLAG_BITEXACT) && !(codec_flags & CODEC_FLAG_BITEXACT))
		av_strlcpy((char *)encoder_string, LIBAVCODEC_IDENT " ", encoder_string_len);
	else
		av_strlcpy((char *)encoder_string, "Lavc ", encoder_string_len);
	av_strlcat((char *)encoder_string, ost->enc->name, encoder_string_len);
	av_dict_set(&ost->st->metadata, "encoder", (char *)encoder_string,
		AV_DICT_DONT_STRDUP_VAL | AV_DICT_DONT_OVERWRITE);
}

static int transcode_init(void)
{
	int ret = 0, i, j, k;
	AVFormatContext *oc;
	OutputStream *ost;
	InputStream *ist;
	char error[1024] = { 0 };
	int want_sdp = 1;

	for (i = 0; i < nb_filtergraphs; i++) {  //nb_filtergraphs=0
		FilterGraph *fg = filtergraphs[i];
		for (j = 0; j < fg->nb_outputs; j++) {
			OutputFilter *ofilter = fg->outputs[j];
			if (!ofilter->ost || ofilter->ost->source_index >= 0)
				continue;
			if (fg->nb_inputs != 1)
				continue;
			for (k = nb_input_streams - 1; k >= 0; k--)
			if (fg->inputs[0]->ist == input_streams[k])
				break;
			ofilter->ost->source_index = k;
		}
	}

	/* init framerate emulation 初始化帧率仿真（转换时是不按帧率来的，但如果要求帧率仿真，就可以做到）*/
	for (i = 0; i < nb_input_files; i++) {  //nb_input_files表示输入的文件数
		InputFile *ifile = input_files[i];
		//如果一个输入文件被要求帧率仿真（指的是即使是转换也像播放那样按照帧率来进行
		//则为这个文件中的所有流记录下开始时间
		if (ifile->rate_emu)
		for (j = 0; j < ifile->nb_streams; j++)
			input_streams[j + ifile->ist_index]->start = av_gettime_relative();
	}

	/* for each output stream, we compute the right encoding parameters */
	//轮循所有的输出流，根据对应的输入流，设置其编解码器的参数
	for (i = 0; i < nb_output_streams; i++) { //nb_output_streams表示输出流，可有音频/视频等
		AVCodecContext *enc_ctx;
		AVCodecContext *dec_ctx = NULL;
		ost = output_streams[i];    //循环所有的输出流
		oc = output_files[ost->file_index]->ctx;    //每个输出流对应的FormatContext
		ist = get_input_stream(ost);    //取得输出流对应的输入流

		if (ost->attachment_filename)
			continue;

		enc_ctx = ost->stream_copy ? ost->st->codec : ost->enc_ctx;

		if (ist) {
			dec_ctx = ist->dec_ctx;

			ost->st->disposition = ist->st->disposition;
			enc_ctx->bits_per_raw_sample = dec_ctx->bits_per_raw_sample;
			enc_ctx->chroma_sample_location = dec_ctx->chroma_sample_location;
		}
		else {
			for (j = 0; j<oc->nb_streams; j++) {
				AVStream *st = oc->streams[j];
				if (st != ost->st && st->codec->codec_type == enc_ctx->codec_type)
					break;
			}
			if (j == oc->nb_streams)
			if (enc_ctx->codec_type == AVMEDIA_TYPE_AUDIO || enc_ctx->codec_type == AVMEDIA_TYPE_VIDEO)
				ost->st->disposition = AV_DISPOSITION_DEFAULT;
		}

		//如果只是复制一个流，不用编解码，则把输入流的编码参数直接复制给输出流
		//此时是不需要解码也不用编码，所以不打开编码器和解码器
		if (ost->stream_copy) {
			AVRational sar;
			uint64_t extra_size;

			av_assert0(ist && !ost->filter);

			//计算输出流的编解码器的extradata的大小，然后分配容纳extradata的缓冲
			//然后把输入流的编解码器的extradata复制到输出流的编解码器中
			extra_size = (uint64_t)dec_ctx->extradata_size + AV_INPUT_BUFFER_PADDING_SIZE;

			if (extra_size > INT_MAX) {
				return AVERROR(EINVAL);
			}

			/* if stream_copy is selected, no need to decode or encode */
			enc_ctx->codec_id = dec_ctx->codec_id;
			enc_ctx->codec_type = dec_ctx->codec_type;

			if (!enc_ctx->codec_tag) {
				unsigned int codec_tag;
				if (!oc->oformat->codec_tag ||
					av_codec_get_id(oc->oformat->codec_tag, dec_ctx->codec_tag) == enc_ctx->codec_id ||
					!av_codec_get_tag2(oc->oformat->codec_tag, dec_ctx->codec_id, &codec_tag))
					enc_ctx->codec_tag = dec_ctx->codec_tag;
			}

			enc_ctx->bit_rate = dec_ctx->bit_rate;
			enc_ctx->rc_max_rate = dec_ctx->rc_max_rate;
			enc_ctx->rc_buffer_size = dec_ctx->rc_buffer_size;
			enc_ctx->field_order = dec_ctx->field_order;
			if (dec_ctx->extradata_size) {
				enc_ctx->extradata = (uint8_t *)av_mallocz(extra_size);
				if (!enc_ctx->extradata) {
					return AVERROR(ENOMEM);
				}
				memcpy(enc_ctx->extradata, dec_ctx->extradata, dec_ctx->extradata_size);
			}
			enc_ctx->extradata_size = dec_ctx->extradata_size;
			enc_ctx->bits_per_coded_sample = dec_ctx->bits_per_coded_sample;

			//这是帧率
			enc_ctx->time_base = ist->st->time_base;
			/*
			* Avi is a special case here because it supports variable fps but
			* having the fps and timebase differe significantly adds quite some
			* overhead
			*/
			//如果输出文件是avi，做一点特殊处理
			if (!strcmp(oc->oformat->name, "avi")) {
				if (copy_tb<0 && av_q2d(ist->st->r_frame_rate) >= av_q2d(ist->st->avg_frame_rate)
					&& 0.5 / av_q2d(ist->st->r_frame_rate) > av_q2d(ist->st->time_base)
					&& 0.5 / av_q2d(ist->st->r_frame_rate) > av_q2d(dec_ctx->time_base)
					&& av_q2d(ist->st->time_base) < 1.0 / 500 && av_q2d(dec_ctx->time_base) < 1.0 / 500
					|| copy_tb == 2){
					enc_ctx->time_base.num = ist->st->r_frame_rate.den;
					enc_ctx->time_base.den = 2 * ist->st->r_frame_rate.num;
					enc_ctx->ticks_per_frame = 2;
				}
				else if (copy_tb<0 && av_q2d(dec_ctx->time_base)*dec_ctx->ticks_per_frame > 2 * av_q2d(ist->st->time_base)
					&& av_q2d(ist->st->time_base) < 1.0 / 500
					|| copy_tb == 0){
					enc_ctx->time_base = dec_ctx->time_base;
					enc_ctx->time_base.num *= dec_ctx->ticks_per_frame;
					enc_ctx->time_base.den *= 2;
					enc_ctx->ticks_per_frame = 2;
				}
			}
			else if (!(oc->oformat->flags & AVFMT_VARIABLE_FPS)
				&& strcmp(oc->oformat->name, "mov") && strcmp(oc->oformat->name, "mp4") && strcmp(oc->oformat->name, "3gp")
				&& strcmp(oc->oformat->name, "3g2") && strcmp(oc->oformat->name, "psp") && strcmp(oc->oformat->name, "ipod")
				&& strcmp(oc->oformat->name, "f4v")
				) {
				if (copy_tb<0 && dec_ctx->time_base.den
					&& av_q2d(dec_ctx->time_base)*dec_ctx->ticks_per_frame > av_q2d(ist->st->time_base)
					&& av_q2d(ist->st->time_base) < 1.0 / 500
					|| copy_tb == 0){
					enc_ctx->time_base = dec_ctx->time_base;
					enc_ctx->time_base.num *= dec_ctx->ticks_per_frame;
				}
			}
			if (enc_ctx->codec_tag == AV_RL32("tmcd")
				&& dec_ctx->time_base.num < dec_ctx->time_base.den
				&& dec_ctx->time_base.num > 0
				&& 121LL * dec_ctx->time_base.num > dec_ctx->time_base.den) {
				enc_ctx->time_base = dec_ctx->time_base;
			}

			if (ist && !ost->frame_rate.num)
				ost->frame_rate = ist->framerate;
			if (ost->frame_rate.num)
				enc_ctx->time_base = av_inv_q(ost->frame_rate);

			//再修正一下帧率
			av_reduce(&enc_ctx->time_base.num, &enc_ctx->time_base.den,
				enc_ctx->time_base.num, enc_ctx->time_base.den, INT_MAX);

			if (ist->st->nb_side_data) {
				ost->st->side_data = (AVPacketSideData*)av_realloc_array(NULL, ist->st->nb_side_data,
					sizeof(*ist->st->side_data));
				if (!ost->st->side_data)
					return AVERROR(ENOMEM);

				ost->st->nb_side_data = 0;
				for (j = 0; j < ist->st->nb_side_data; j++) {
					const AVPacketSideData *sd_src = &ist->st->side_data[j];
					AVPacketSideData *sd_dst = &ost->st->side_data[ost->st->nb_side_data];

					if (ost->rotate_overridden && sd_src->type == AV_PKT_DATA_DISPLAYMATRIX)
						continue;

					sd_dst->data = (uint8_t *)av_malloc(sd_src->size);
					if (!sd_dst->data)
						return AVERROR(ENOMEM);
					memcpy(sd_dst->data, sd_src->data, sd_src->size);
					sd_dst->size = sd_src->size;
					sd_dst->type = sd_src->type;
					ost->st->nb_side_data++;
				}
			}

			ost->parser = av_parser_init(enc_ctx->codec_id);

			//单独复制不同媒体自己的编码参数
			switch (enc_ctx->codec_type) {
			case AVMEDIA_TYPE_AUDIO:     //音频
				if (audio_volume != 256) {
					av_log(NULL, AV_LOG_FATAL, "-acodec copy and -vol are incompatible (frames are not decoded)\n");
					exit_program(1);
				}
				enc_ctx->channel_layout = dec_ctx->channel_layout;
				enc_ctx->sample_rate = dec_ctx->sample_rate;
				enc_ctx->channels = dec_ctx->channels;
				enc_ctx->frame_size = dec_ctx->frame_size;
				enc_ctx->audio_service_type = dec_ctx->audio_service_type;
				enc_ctx->block_align = dec_ctx->block_align;
				enc_ctx->initial_padding = dec_ctx->delay;
#if FF_API_AUDIOENC_DELAY
				enc_ctx->delay = dec_ctx->delay;
#endif
				if ((enc_ctx->block_align == 1 || enc_ctx->block_align == 1152 || enc_ctx->block_align == 576) && enc_ctx->codec_id == AV_CODEC_ID_MP3)
					enc_ctx->block_align = 0;
				if (enc_ctx->codec_id == AV_CODEC_ID_AC3)
					enc_ctx->block_align = 0;
				break;
			case AVMEDIA_TYPE_VIDEO:
				enc_ctx->pix_fmt = dec_ctx->pix_fmt;
				enc_ctx->width = dec_ctx->width;
				enc_ctx->height = dec_ctx->height;
				enc_ctx->has_b_frames = dec_ctx->has_b_frames;
				if (ost->frame_aspect_ratio.num) { // overridden by the -aspect cli option
					sar =
						av_mul_q(ost->frame_aspect_ratio, { enc_ctx->height, enc_ctx->width });
					av_log(NULL, AV_LOG_WARNING, "Overriding aspect ratio "
						"with stream copy may produce invalid files\n");
				}
				else if (ist->st->sample_aspect_ratio.num)
					sar = ist->st->sample_aspect_ratio;
				else
					sar = dec_ctx->sample_aspect_ratio;
				ost->st->sample_aspect_ratio = enc_ctx->sample_aspect_ratio = sar;
				ost->st->avg_frame_rate = ist->st->avg_frame_rate;
				ost->st->r_frame_rate = ist->st->r_frame_rate;
				break;
			case AVMEDIA_TYPE_SUBTITLE:
				enc_ctx->width = dec_ctx->width;
				enc_ctx->height = dec_ctx->height;
				break;
			case AVMEDIA_TYPE_UNKNOWN:
			case AVMEDIA_TYPE_DATA:
			case AVMEDIA_TYPE_ATTACHMENT:
				break;
			default:
				abort();
			}
		}
		else {
			if (!ost->enc)    //获取编码器
				ost->enc = avcodec_find_encoder(enc_ctx->codec_id);
			if (!ost->enc) {
				/* should only happen when a default codec is not present. */
				_snprintf(error, sizeof(error), "Encoder (codec %s) not found for output stream #%d:%d",
					avcodec_get_name(ost->st->codec->codec_id), ost->file_index, ost->index);
				ret = AVERROR(EINVAL);
				goto dump_format;
			}

			set_encoder_id(output_files[ost->file_index], ost);

			if (!ost->filter &&
				(enc_ctx->codec_type == AVMEDIA_TYPE_VIDEO ||
				enc_ctx->codec_type == AVMEDIA_TYPE_AUDIO)) {
				FilterGraph *fg;
				fg = init_simple_filtergraph(ist, ost);
				if (configure_filtergraph(fg)) {
					av_log(NULL, AV_LOG_FATAL, "Error opening filters!\n");
					exit_program(1);
				}
			}

			if (enc_ctx->codec_type == AVMEDIA_TYPE_VIDEO) {
				if (!ost->frame_rate.num)    //这里都是在计算帧率
					ost->frame_rate = av_buffersink_get_frame_rate(ost->filter->filter);
				if (ist && !ost->frame_rate.num)
					ost->frame_rate = ist->framerate;
				if (ist && !ost->frame_rate.num)
					ost->frame_rate = ist->st->r_frame_rate;
				if (ist && !ost->frame_rate.num) {
					ost->frame_rate = { 25, 1 };
					av_log(NULL, AV_LOG_WARNING,
						"No information "
						"about the input framerate is available. Falling "
						"back to a default value of 25fps for output stream #%d:%d. Use the -r option "
						"if you want a different framerate.\n",
						ost->file_index, ost->index);
				}
				//                    ost->frame_rate = ist->st->avg_frame_rate.num ? ist->st->avg_frame_rate : (AVRational){25, 1};
				if (ost->enc && ost->enc->supported_framerates && !ost->force_fps) {
					int idx = av_find_nearest_q_idx(ost->frame_rate, ost->enc->supported_framerates);
					ost->frame_rate = ost->enc->supported_framerates[idx];
				}
				// reduce frame rate for mpeg4 to be within the spec limits
				if (enc_ctx->codec_id == AV_CODEC_ID_MPEG4) {
					av_reduce(&ost->frame_rate.num, &ost->frame_rate.den,
						ost->frame_rate.num, ost->frame_rate.den, 65535);
				}
			}

			switch (enc_ctx->codec_type) {
			case AVMEDIA_TYPE_AUDIO:
				enc_ctx->sample_fmt = (AVSampleFormat)ost->filter->filter->inputs[0]->format;    //样点格式
				enc_ctx->sample_rate = ost->filter->filter->inputs[0]->sample_rate;   //采样率
				enc_ctx->channel_layout = ost->filter->filter->inputs[0]->channel_layout;
				enc_ctx->channels = avfilter_link_get_channels(ost->filter->filter->inputs[0]);
				enc_ctx->time_base = { 1, enc_ctx->sample_rate };
				break;
			case AVMEDIA_TYPE_VIDEO:
				enc_ctx->time_base = av_inv_q(ost->frame_rate);
				if (!(enc_ctx->time_base.num && enc_ctx->time_base.den))
					enc_ctx->time_base = ost->filter->filter->inputs[0]->time_base;
				if (av_q2d(enc_ctx->time_base) < 0.001 && video_sync_method != VSYNC_PASSTHROUGH
					&& (video_sync_method == VSYNC_CFR || video_sync_method == VSYNC_VSCFR || (video_sync_method == VSYNC_AUTO && !(oc->oformat->flags & AVFMT_VARIABLE_FPS)))){
					av_log(oc, AV_LOG_WARNING, "Frame rate very high for a muxer not efficiently supporting it.\n"
						"Please consider specifying a lower framerate, a different muxer or -vsync 2\n");
				}
				for (j = 0; j < ost->forced_kf_count; j++)
					ost->forced_kf_pts[j] = av_rescale_q(ost->forced_kf_pts[j],
					{ 1, AV_TIME_BASE },
					enc_ctx->time_base);

				enc_ctx->width = ost->filter->filter->inputs[0]->w;
				enc_ctx->height = ost->filter->filter->inputs[0]->h;
				enc_ctx->sample_aspect_ratio = ost->st->sample_aspect_ratio =
					ost->frame_aspect_ratio.num ? // overridden by the -aspect cli option
					av_mul_q(ost->frame_aspect_ratio, { enc_ctx->height, enc_ctx->width }) :
					ost->filter->filter->inputs[0]->sample_aspect_ratio;
				if (!strncmp(ost->enc->name, "libx264", 7) &&
					enc_ctx->pix_fmt == AV_PIX_FMT_NONE &&
					ost->filter->filter->inputs[0]->format != AV_PIX_FMT_YUV420P)
					av_log(NULL, AV_LOG_WARNING,
					"No pixel format specified, %s for H.264 encoding chosen.\n"
					"Use -pix_fmt yuv420p for compatibility with outdated media players.\n",
					av_get_pix_fmt_name((AVPixelFormat)ost->filter->filter->inputs[0]->format));
				if (!strncmp(ost->enc->name, "mpeg2video", 10) &&
					enc_ctx->pix_fmt == AV_PIX_FMT_NONE &&
					ost->filter->filter->inputs[0]->format != AV_PIX_FMT_YUV420P)
					av_log(NULL, AV_LOG_WARNING,
					"No pixel format specified, %s for MPEG-2 encoding chosen.\n"
					"Use -pix_fmt yuv420p for compatibility with outdated media players.\n",
					av_get_pix_fmt_name((AVPixelFormat)ost->filter->filter->inputs[0]->format));
				enc_ctx->pix_fmt = (AVPixelFormat)ost->filter->filter->inputs[0]->format;

				ost->st->avg_frame_rate = ost->frame_rate;

				if (!dec_ctx ||
					enc_ctx->width != dec_ctx->width ||
					enc_ctx->height != dec_ctx->height ||
					enc_ctx->pix_fmt != dec_ctx->pix_fmt) {
					enc_ctx->bits_per_raw_sample = frame_bits_per_raw_sample;
				}

				if (ost->forced_keyframes) {
					if (!strncmp((char *)ost->forced_keyframes, "expr:", 5)) {
						ret = av_expr_parse(&ost->forced_keyframes_pexpr, (char *)ost->forced_keyframes + 5,
							forced_keyframes_const_names, NULL, NULL, NULL, NULL, 0, NULL);
						if (ret < 0) {
							av_log(NULL, AV_LOG_ERROR,
								"Invalid force_key_frames expression '%s'\n", ost->forced_keyframes + 5);
							return ret;
						}
						ost->forced_keyframes_expr_const_values[FKF_N] = 0;
						ost->forced_keyframes_expr_const_values[FKF_N_FORCED] = 0;
						ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_N] = NAN;
						ost->forced_keyframes_expr_const_values[FKF_PREV_FORCED_T] = NAN;

						// Don't parse the 'forced_keyframes' in case of 'keep-source-keyframes',
						// parse it only for static kf timings
					}
					else if (strncmp((char *)ost->forced_keyframes, "source", 6)) {
						parse_forced_key_frames((char *)ost->forced_keyframes, ost, ost->enc_ctx);
					}
				}
				break;
			case AVMEDIA_TYPE_SUBTITLE:
				enc_ctx->time_base = { 1, 1000 };
				if (!enc_ctx->width) {
					enc_ctx->width = input_streams[ost->source_index]->st->codec->width;
					enc_ctx->height = input_streams[ost->source_index]->st->codec->height;
				}
				break;
			case AVMEDIA_TYPE_DATA:
				break;
			default:
				abort();
				break;
			}
		}

		if (ost->disposition) {
			static  AVOption opts[15] = {
				{ "disposition", NULL, 0, AV_OPT_TYPE_FLAGS, 0, INT64_MIN, INT64_MAX },
				{ "default", NULL, 0, AV_OPT_TYPE_CONST },
				{ "dub", NULL, 0, AV_OPT_TYPE_CONST },
				{ "original", NULL, 0, AV_OPT_TYPE_CONST },
				{ "comment", NULL, 0, AV_OPT_TYPE_CONST },
				{ "lyrics", NULL, 0, AV_OPT_TYPE_CONST },
				{ "karaoke", NULL, 0, AV_OPT_TYPE_CONST },
				{ "forced", NULL, 0, AV_OPT_TYPE_CONST },
				{ "hearing_impaired", NULL, 0, AV_OPT_TYPE_CONST },
				{ "visual_impaired", NULL, 0, AV_OPT_TYPE_CONST },
				{ "clean_effects", NULL, 0, AV_OPT_TYPE_CONST },
				{ "captions", NULL, 0, AV_OPT_TYPE_CONST },
				{ "descriptions", NULL, 0, AV_OPT_TYPE_CONST },
				{ "metadata", NULL, 0, AV_OPT_TYPE_CONST },
				{ NULL },
			};
			for (int i = 0; i < 15; i++)
				opts[i].unit = "flags";
			opts[1].default_val.i64 = AV_DISPOSITION_DEFAULT;
			opts[2].default_val.i64 = AV_DISPOSITION_DUB;
			opts[3].default_val.i64 = AV_DISPOSITION_ORIGINAL;
			opts[4].default_val.i64 = AV_DISPOSITION_COMMENT;
			opts[5].default_val.i64 = AV_DISPOSITION_LYRICS;
			opts[6].default_val.i64 = AV_DISPOSITION_KARAOKE;
			opts[7].default_val.i64 = AV_DISPOSITION_FORCED;
			opts[8].default_val.i64 = AV_DISPOSITION_HEARING_IMPAIRED;
			opts[9].default_val.i64 = AV_DISPOSITION_VISUAL_IMPAIRED;
			opts[10].default_val.i64 = AV_DISPOSITION_CLEAN_EFFECTS;
			opts[11].default_val.i64 = AV_DISPOSITION_CAPTIONS;
			opts[12].default_val.i64 = AV_DISPOSITION_DESCRIPTIONS;
			opts[13].default_val.i64 = AV_DISPOSITION_METADATA;

			static  AVClass class_1;
			class_1.class_name = "";
			class_1.item_name = av_default_item_name;
			class_1.option = opts;
			class_1.version = LIBAVUTIL_VERSION_INT;

			const AVClass *pclass = &class_1;

			ret = av_opt_eval_flags(&pclass, &opts[0], (char *)ost->disposition, &ost->st->disposition);
			if (ret < 0)
				goto dump_format;
		}
	}

	/* open each encoder 打开每个输出流的编码器*/
	for (i = 0; i < nb_output_streams; i++) {
		ret = init_output_stream(output_streams[i], error, sizeof(error));
		if (ret < 0)
			goto dump_format;
	}

	/* init input streams 初始化所有的输入流，主要就是在需要的时候打开解码器*/
	for (i = 0; i < nb_input_streams; i++)
	if ((ret = init_input_stream(i, error, sizeof(error))) < 0) {
		for (i = 0; i < nb_output_streams; i++) {
			ost = output_streams[i];
			avcodec_close(ost->enc_ctx);
		}
		goto dump_format;
	}

	/* discard unused programs */
	for (i = 0; i < nb_input_files; i++) {
		InputFile *ifile = input_files[i];
		for (j = 0; j < ifile->ctx->nb_programs; j++) {
			AVProgram *p = ifile->ctx->programs[j];
			int discard = AVDISCARD_ALL;

			for (k = 0; k < p->nb_stream_indexes; k++)
			if (!input_streams[ifile->ist_index + p->stream_index[k]]->discard) {
				discard = AVDISCARD_DEFAULT;
				break;
			}
			p->discard = (AVDiscard)discard;
		}
	}

	/* open files and write file headers 打开所有的输出文件，写入媒体文件头*/
	for (i = 0; i < nb_output_files; i++) {
		oc = output_files[i]->ctx;
		oc->interrupt_callback = int_cb;
		if ((ret = avformat_write_header(oc, &output_files[i]->opts)) < 0) {
			_snprintf(error, sizeof(error),
				"Could not write header for output file #%d "
				"(incorrect codec parameters ?): %s",
				i, av_err2str(ret));
			ret = AVERROR(EINVAL);
			goto dump_format;
		}
		//         assert_avoptions(output_files[i]->opts);
		if (strcmp(oc->oformat->name, "rtp")) {
			want_sdp = 0;
		}
	}

dump_format:
	/* dump the file output parameters - cannot be done before in case
	of stream copy */
	for (i = 0; i < nb_output_files; i++) {
		//在屏幕上打印输出格式信息．注意这里是输出的格式信息，输入格式信息是在parse_option函数执行中打印输出的
		av_dump_format(output_files[i]->ctx, i, output_files[i]->ctx->filename, 1);
	}

	/* dump the stream mapping */
	av_log(NULL, AV_LOG_INFO, "Stream mapping:\n");
	for (i = 0; i < nb_input_streams; i++) {
		ist = input_streams[i];

		for (j = 0; j < ist->nb_filters; j++) {
			if (ist->filters[j]->graph->graph_desc) {
				av_log(NULL, AV_LOG_INFO, "  Stream #%d:%d (%s) -> %s",
					ist->file_index, ist->st->index, ist->dec ? ist->dec->name : "?",
					ist->filters[j]->name);
				if (nb_filtergraphs > 1)
					av_log(NULL, AV_LOG_INFO, " (graph %d)", ist->filters[j]->graph->index);
				av_log(NULL, AV_LOG_INFO, "\n");
			}
		}
	}

	for (i = 0; i < nb_output_streams; i++) {
		ost = output_streams[i];

		if (ost->attachment_filename) {
			/* an attached file */
			av_log(NULL, AV_LOG_INFO, "  File %s -> Stream #%d:%d\n",
				ost->attachment_filename, ost->file_index, ost->index);
			continue;
		}

		if (ost->filter && ost->filter->graph->graph_desc) {
			/* output from a complex graph */
			av_log(NULL, AV_LOG_INFO, "  %s", ost->filter->name);
			if (nb_filtergraphs > 1)
				av_log(NULL, AV_LOG_INFO, " (graph %d)", ost->filter->graph->index);

			av_log(NULL, AV_LOG_INFO, " -> Stream #%d:%d (%s)\n", ost->file_index,
				ost->index, ost->enc ? ost->enc->name : "?");
			continue;
		}

		av_log(NULL, AV_LOG_INFO, "  Stream #%d:%d -> #%d:%d",
			input_streams[ost->source_index]->file_index,
			input_streams[ost->source_index]->st->index,
			ost->file_index,
			ost->index);
		if (ost->sync_ist != input_streams[ost->source_index])
			av_log(NULL, AV_LOG_INFO, " [sync #%d:%d]",
			ost->sync_ist->file_index,
			ost->sync_ist->st->index);
		if (ost->stream_copy)
			av_log(NULL, AV_LOG_INFO, " (copy)");
		else {
			const AVCodec *in_codec = input_streams[ost->source_index]->dec;
			const AVCodec *out_codec = ost->enc;
			const char *decoder_name = "?";
			const char *in_codec_name = "?";
			const char *encoder_name = "?";
			const char *out_codec_name = "?";
			const AVCodecDescriptor *desc;

			if (in_codec) {
				decoder_name = in_codec->name;  //mpeg2video
				desc = avcodec_descriptor_get(in_codec->id);
				if (desc)
					in_codec_name = desc->name;  //mpeg2video
				if (!strcmp(decoder_name, in_codec_name))
					decoder_name = "native";
			}

			if (out_codec) {
				encoder_name = out_codec->name;
				desc = avcodec_descriptor_get(out_codec->id);
				if (desc)
					out_codec_name = desc->name;
				if (!strcmp(encoder_name, out_codec_name))
					encoder_name = "native";
			}

			av_log(NULL, AV_LOG_INFO, " (%s (%s) -> %s (%s))",
				in_codec_name, decoder_name,
				out_codec_name, encoder_name);
		}
		av_log(NULL, AV_LOG_INFO, "\n");
	}

	if (ret) {
		av_log(NULL, AV_LOG_ERROR, "%s\n", error);
		return ret;
	}

	if (sdp_filename || want_sdp) {
		print_sdp();
	}

	transcode_init_done = 1;

	return 0;
}

/* Return 1 if there remain streams where more output is wanted, 0 otherwise. */
static int need_output(void)
{
	int i;

	for (i = 0; i < nb_output_streams; i++) {    //分为音频，视频，字幕等流
		OutputStream *ost = output_streams[i];
		OutputFile *of = output_files[ost->file_index];
		AVFormatContext *os = output_files[ost->file_index]->ctx;

		if (ost->finished ||
			(os->pb && avio_tell(os->pb) >= of->limit_filesize))
			continue;
		if (ost->frame_number >= ost->max_frames) {
			int j;
			for (j = 0; j < of->ctx->nb_streams; j++)
				close_output_stream(output_streams[of->ost_index + j]);
			continue;
		}

		return 1;
	}

	return 0;
}

/**
* Select the output stream to process.
*
* @return  selected output stream, or NULL if none available
*/
static OutputStream *choose_output(void)
{
	int i;
	int64_t opts_min = INT64_MAX;
	OutputStream *ost_min = NULL;

	for (i = 0; i < nb_output_streams; i++) {    //nb_output_streams为输出流的个数，可以是音频，视频，字幕等
		OutputStream *ost = output_streams[i];
		int64_t opts = av_rescale_q(ost->st->cur_dts, ost->st->time_base,
		{ 1, AV_TIME_BASE });
		if (!ost->finished && opts < opts_min) {   //选择当前视频或者音频中时间戳较小的一个作为输出流处理
			opts_min = opts;
			ost_min = ost->unavailable ? NULL : ost;
		}
	}
	return ost_min;
}

static int check_keyboard_interaction(int64_t cur_time)
{
	int i, ret, key;
	static int64_t last_time;
	if (received_nb_signals)
		return AVERROR_EXIT;
	/* read_key() returns 0 on EOF */
	if (cur_time - last_time >= 100000 && !run_as_daemon){
		key = read_key();
		last_time = cur_time;
	}
	else
		key = -1;
	if (key == 'q')
		return AVERROR_EXIT;
	if (key == '+') av_log_set_level(av_log_get_level() + 10);
	if (key == '-') av_log_set_level(av_log_get_level() - 10);
	if (key == 's') qp_hist ^= 1;
	if (key == 'h'){
		if (do_hex_dump){
			do_hex_dump = do_pkt_dump = 0;
		}
		else if (do_pkt_dump){
			do_hex_dump = 1;
		}
		else
			do_pkt_dump = 1;
		av_log_set_level(AV_LOG_DEBUG);
	}
	if (key == 'c' || key == 'C'){
		char buf[4096], target[64], command[256], arg[256] = { 0 };
		double time;
		int k, n = 0;
		fprintf(stderr, "\nEnter command: <target>|all <time>|-1 <command>[ <argument>]\n");
		i = 0;
		while ((k = read_key()) != '\n' && k != '\r' && i < sizeof(buf)-1)
		if (k > 0)
			buf[i++] = k;
		buf[i] = 0;
		if (k > 0 &&
			(n = sscanf(buf, "%63[^ ] %lf %255[^ ] %255[^\n]", target, &time, command, arg)) >= 3) {
			av_log(NULL, AV_LOG_DEBUG, "Processing command target:%s time:%f command:%s arg:%s",
				target, time, command, arg);
			for (i = 0; i < nb_filtergraphs; i++) {
				FilterGraph *fg = filtergraphs[i];
				if (fg->graph) {
					if (time < 0) {
						ret = avfilter_graph_send_command(fg->graph, target, command, arg, buf, sizeof(buf),
							key == 'c' ? AVFILTER_CMD_FLAG_ONE : 0);
						fprintf(stderr, "Command reply for stream %d: ret:%d res:\n%s", i, ret, buf);
					}
					else if (key == 'c') {
						fprintf(stderr, "Queing commands only on filters supporting the specific command is unsupported\n");
						ret = AVERROR_PATCHWELCOME;
					}
					else {
						ret = avfilter_graph_queue_command(fg->graph, target, command, arg, 0, time);
						if (ret < 0)
							fprintf(stderr, "Queing command failed with error %s\n", av_err2str(ret));
					}
				}
			}
		}
		else {
			av_log(NULL, AV_LOG_ERROR,
				"Parse error, at least 3 arguments were expected, "
				"only %d given in string '%s'\n", n, buf);
		}
	}
	if (key == 'd' || key == 'D'){
		int debug = 0;
		if (key == 'D') {
			debug = input_streams[0]->st->codec->debug << 1;
			if (!debug) debug = 1;
			while (debug & (FF_DEBUG_DCT_COEFF | FF_DEBUG_VIS_QP | FF_DEBUG_VIS_MB_TYPE)) //unsupported, would just crash
				debug += debug;
		}
		else
		if (scanf("%d", &debug) != 1)
			fprintf(stderr, "error parsing debug value\n");
		for (i = 0; i<nb_input_streams; i++) {
			input_streams[i]->st->codec->debug = debug;
		}
		for (i = 0; i<nb_output_streams; i++) {
			OutputStream *ost = output_streams[i];
			ost->enc_ctx->debug = debug;
		}
		if (debug) av_log_set_level(AV_LOG_DEBUG);
		fprintf(stderr, "debug=%d\n", debug);
	}
	if (key == '?'){
		fprintf(stderr, "key    function\n"
			"?      show this help\n"
			"+      increase verbosity\n"
			"-      decrease verbosity\n"
			"c      Send command to first matching filter supporting it\n"
			"C      Send/Que command to all matching filters\n"
			"D      cycle through available debug modes\n"
			"h      dump packets/hex press to cycle through the 3 states\n"
			"q      quit\n"
			"s      Show QP histogram\n"
			);
	}
	return 0;
}

#if HAVE_PTHREADS
static void *input_thread(void *arg)
{
	InputFile *f = arg;
	unsigned flags = f->non_blocking ? AV_THREAD_MESSAGE_NONBLOCK : 0;
	int ret = 0;

	while (1) {
		AVPacket pkt;
		ret = av_read_frame(f->ctx, &pkt);

		if (ret == AVERROR(EAGAIN)) {
			av_usleep(10000);
			continue;
		}
		if (ret < 0) {
			av_thread_message_queue_set_err_recv(f->in_thread_queue, ret);
			break;
		}
		av_dup_packet(&pkt);
		ret = av_thread_message_queue_send(f->in_thread_queue, &pkt, flags);
		if (flags && ret == AVERROR(EAGAIN)) {
			flags = 0;
			ret = av_thread_message_queue_send(f->in_thread_queue, &pkt, flags);
			av_log(f->ctx, AV_LOG_WARNING,
				"Thread message queue blocking; consider raising the "
				"thread_queue_size option (current value: %d)\n",
				f->thread_queue_size);
		}
		if (ret < 0) {
			if (ret != AVERROR_EOF)
				av_log(f->ctx, AV_LOG_ERROR,
				"Unable to send packet to main thread: %s\n",
				av_err2str(ret));
			av_free_packet(&pkt);
			av_thread_message_queue_set_err_recv(f->in_thread_queue, ret);
			break;
		}
	}

	return NULL;
}

static void free_input_threads(void)
{
	int i;

	for (i = 0; i < nb_input_files; i++) {
		InputFile *f = input_files[i];
		AVPacket pkt;

		if (!f || !f->in_thread_queue)
			continue;
		av_thread_message_queue_set_err_send(f->in_thread_queue, AVERROR_EOF);
		while (av_thread_message_queue_recv(f->in_thread_queue, &pkt, 0) >= 0)
			av_free_packet(&pkt);

		pthread_join(f->thread, NULL);
		f->joined = 1;
		av_thread_message_queue_free(&f->in_thread_queue);
	}
}

static int init_input_threads(void)
{
	int i, ret;

	if (nb_input_files == 1)
		return 0;

	for (i = 0; i < nb_input_files; i++) {
		InputFile *f = input_files[i];

		if (f->ctx->pb ? !f->ctx->pb->seekable :
			strcmp(f->ctx->iformat->name, "lavfi"))
			f->non_blocking = 1;
		ret = av_thread_message_queue_alloc(&f->in_thread_queue,
			f->thread_queue_size, sizeof(AVPacket));
		if (ret < 0)
			return ret;

		if ((ret = pthread_create(&f->thread, NULL, input_thread, f))) {
			av_log(NULL, AV_LOG_ERROR, "pthread_create failed: %s. Try to increase `ulimit -v` or decrease `ulimit -s`.\n", strerror(ret));
			av_thread_message_queue_free(&f->in_thread_queue);
			return AVERROR(ret);
		}
	}
	return 0;
}

static int get_input_packet_mt(InputFile *f, AVPacket *pkt)
{
	return av_thread_message_queue_recv(f->in_thread_queue, pkt,
		f->non_blocking ?
	AV_THREAD_MESSAGE_NONBLOCK : 0);
}
#endif

static int get_input_packet(InputFile *f, AVPacket *pkt)
{
	if (f->rate_emu) {
		int i;
		for (i = 0; i < f->nb_streams; i++) {
			InputStream *ist = input_streams[f->ist_index + i];
			int64_t pts = av_rescale(ist->dts, 1000000, AV_TIME_BASE);
			int64_t now = av_gettime_relative() - ist->start;
			if (pts > now)
				return AVERROR(EAGAIN);
		}
	}

#if HAVE_PTHREADS
	if (nb_input_files > 1)
		return get_input_packet_mt(f, pkt);
#endif
	return av_read_frame(f->ctx, pkt);
}

static int got_eagain(void)
{
	int i;
	for (i = 0; i < nb_output_streams; i++)
	if (output_streams[i]->unavailable)
		return 1;
	return 0;
}

static void reset_eagain(void)
{
	int i;
	for (i = 0; i < nb_input_files; i++)
		input_files[i]->eagain = 0;
	for (i = 0; i < nb_output_streams; i++)
		output_streams[i]->unavailable = 0;
}

/*
* Return
* - 0 -- one packet was read and processed
* - AVERROR(EAGAIN) -- no packets were available for selected file,
*   this function should be called again
* - AVERROR_EOF -- this function should not be called again
*/
static int process_input(int file_index)
{
	InputFile *ifile = input_files[file_index];
	AVFormatContext *is;
	InputStream *ist;
	AVPacket pkt;
	int ret, i, j;

	is = ifile->ctx;
	ret = get_input_packet(ifile, &pkt);   //获取一帧压缩编码数据，即一个AVPacket.其中调用了av_read_frame()函数

	if (ret == AVERROR(EAGAIN)) {
		ifile->eagain = 1;
		return ret;
	}
	if (ret < 0) {
		if (ret != AVERROR_EOF) {
			print_error(is->filename, ret);
			if (exit_on_error)
				exit_program(1);
		}

		for (i = 0; i < ifile->nb_streams; i++) {
			ist = input_streams[ifile->ist_index + i];
			if (ist->decoding_needed) {
				ret = process_input_packet(ist, NULL);
				if (ret>0)
					return 0;
			}

			/* mark all outputs that don't go through lavfi as finished */
			for (j = 0; j < nb_output_streams; j++) {
				OutputStream *ost = output_streams[j];

				if (ost->source_index == ifile->ist_index + i &&
					(ost->stream_copy || ost->enc->type == AVMEDIA_TYPE_SUBTITLE))
					finish_output_stream(ost);
			}
		}

		ifile->eof_reached = 1;
		return AVERROR(EAGAIN);
	}

	reset_eagain();    //重新将一些变量置0，

	if (do_pkt_dump) {
		av_pkt_dump_log2(NULL, AV_LOG_DEBUG, &pkt, do_hex_dump,
			is->streams[pkt.stream_index]);
	}
	/* the following test is needed in case new streams appear
	dynamically in stream : we ignore them */
	if (pkt.stream_index >= ifile->nb_streams) {
		report_new_stream(file_index, &pkt);
		goto discard_packet;
	}

	ist = input_streams[ifile->ist_index + pkt.stream_index];

	ist->data_size += pkt.size;
	ist->nb_packets++;

	if (ist->discard)
		goto discard_packet;

	if (!ist->wrap_correction_done && is->start_time != AV_NOPTS_VALUE && ist->st->pts_wrap_bits < 64){
		int64_t stime, stime2;
		// Correcting starttime based on the enabled streams
		// FIXME this ideally should be done before the first use of starttime but we do not know which are the enabled streams at that point.
		//       so we instead do it here as part of discontinuity handling
		if (ist->next_dts == AV_NOPTS_VALUE
			&& ifile->ts_offset == -is->start_time
			&& (is->iformat->flags & AVFMT_TS_DISCONT)) {
			int64_t new_start_time = INT64_MAX;
			for (i = 0; i<is->nb_streams; i++) {
				AVStream *st = is->streams[i];
				if (st->discard == AVDISCARD_ALL || st->start_time == AV_NOPTS_VALUE)
					continue;
				new_start_time = FFMIN(new_start_time, av_rescale_q(st->start_time, st->time_base, { 1, AV_TIME_BASE }));
			}
			if (new_start_time > is->start_time) {
				av_log(is, AV_LOG_VERBOSE, "Correcting start time by %I64d\n", new_start_time - is->start_time);
				ifile->ts_offset = -new_start_time;
			}
		}

		stime = av_rescale_q(is->start_time, { 1, AV_TIME_BASE }, ist->st->time_base);
		stime2 = stime + (1ULL << ist->st->pts_wrap_bits);
		ist->wrap_correction_done = 1;

		if (stime2 > stime && pkt.dts != AV_NOPTS_VALUE && pkt.dts > stime + (1LL << (ist->st->pts_wrap_bits - 1))) {
			pkt.dts -= 1ULL << ist->st->pts_wrap_bits;
			ist->wrap_correction_done = 0;
		}
		if (stime2 > stime && pkt.pts != AV_NOPTS_VALUE && pkt.pts > stime + (1LL << (ist->st->pts_wrap_bits - 1))) {
			pkt.pts -= 1ULL << ist->st->pts_wrap_bits;
			ist->wrap_correction_done = 0;
		}
	}

	/* add the stream-global side data to the first packet */
	if (ist->nb_packets == 1) {    //第一个包如此处理
		if (ist->st->nb_side_data)
			av_packet_split_side_data(&pkt);
		for (i = 0; i < ist->st->nb_side_data; i++) {
			AVPacketSideData *src_sd = &ist->st->side_data[i];
			uint8_t *dst_data;

			if (av_packet_get_side_data(&pkt, src_sd->type, NULL))
				continue;
			if (ist->autorotate && src_sd->type == AV_PKT_DATA_DISPLAYMATRIX)
				continue;

			dst_data = av_packet_new_side_data(&pkt, src_sd->type, src_sd->size);
			if (!dst_data)
				exit_program(1);

			memcpy(dst_data, src_sd->data, src_sd->size);
		}
	}

	if (pkt.dts != AV_NOPTS_VALUE)
		pkt.dts += av_rescale_q(ifile->ts_offset, { 1, AV_TIME_BASE }, ist->st->time_base);
	if (pkt.pts != AV_NOPTS_VALUE)
		pkt.pts += av_rescale_q(ifile->ts_offset, { 1, AV_TIME_BASE }, ist->st->time_base);

	if (pkt.pts != AV_NOPTS_VALUE)
		pkt.pts *= ist->ts_scale;
	if (pkt.dts != AV_NOPTS_VALUE)
		pkt.dts *= ist->ts_scale;

	if ((ist->dec_ctx->codec_type == AVMEDIA_TYPE_VIDEO ||
		ist->dec_ctx->codec_type == AVMEDIA_TYPE_AUDIO) &&
		pkt.dts != AV_NOPTS_VALUE && ist->next_dts == AV_NOPTS_VALUE && !copy_ts
		&& (is->iformat->flags & AVFMT_TS_DISCONT) && ifile->last_ts != AV_NOPTS_VALUE) {
		int64_t pkt_dts = av_rescale_q(pkt.dts, ist->st->time_base, { 1, AV_TIME_BASE });
		int64_t delta = pkt_dts - ifile->last_ts;
		if (delta < -1LL * dts_delta_threshold*AV_TIME_BASE ||
			delta >  1LL * dts_delta_threshold*AV_TIME_BASE){
			ifile->ts_offset -= delta;
			av_log(NULL, AV_LOG_DEBUG,
				"Inter stream timestamp discontinuity %I64d, new offset= %I64d\n",
				delta, ifile->ts_offset);
			pkt.dts -= av_rescale_q(delta, { 1, AV_TIME_BASE }, ist->st->time_base);
			if (pkt.pts != AV_NOPTS_VALUE)
				pkt.pts -= av_rescale_q(delta, { 1, AV_TIME_BASE }, ist->st->time_base);
		}
	}

	if ((ist->dec_ctx->codec_type == AVMEDIA_TYPE_VIDEO ||
		ist->dec_ctx->codec_type == AVMEDIA_TYPE_AUDIO) &&
		pkt.dts != AV_NOPTS_VALUE && ist->next_dts != AV_NOPTS_VALUE &&
		!copy_ts) {
		int64_t pkt_dts = av_rescale_q(pkt.dts, ist->st->time_base, { 1, AV_TIME_BASE });
		int64_t delta = pkt_dts - ist->next_dts;
		if (is->iformat->flags & AVFMT_TS_DISCONT) {
			if (delta < -1LL * dts_delta_threshold*AV_TIME_BASE ||
				delta >  1LL * dts_delta_threshold*AV_TIME_BASE ||
				pkt_dts + AV_TIME_BASE / 10 < FFMAX(ist->pts, ist->dts)) {
				ifile->ts_offset -= delta;
				av_log(NULL, AV_LOG_DEBUG,
					"timestamp discontinuity %I64d, new offset= %I64d\n",
					delta, ifile->ts_offset);
				pkt.dts -= av_rescale_q(delta, { 1, AV_TIME_BASE }, ist->st->time_base);
				if (pkt.pts != AV_NOPTS_VALUE)
					pkt.pts -= av_rescale_q(delta, { 1, AV_TIME_BASE }, ist->st->time_base);
			}
		}
		else {
			if (delta < -1LL * dts_error_threshold*AV_TIME_BASE ||
				delta >  1LL * dts_error_threshold*AV_TIME_BASE) {
				av_log(NULL, AV_LOG_WARNING, "DTS %I64d, next:%I64d st:%d invalid dropping\n", pkt.dts, ist->next_dts, pkt.stream_index);
				pkt.dts = AV_NOPTS_VALUE;
			}
			if (pkt.pts != AV_NOPTS_VALUE){
				int64_t pkt_pts = av_rescale_q(pkt.pts, ist->st->time_base, { 1, AV_TIME_BASE });
				delta = pkt_pts - ist->next_dts;
				if (delta < -1LL * dts_error_threshold*AV_TIME_BASE ||
					delta >  1LL * dts_error_threshold*AV_TIME_BASE) {
					av_log(NULL, AV_LOG_WARNING, "PTS %I64d, next:%I64d invalid dropping st:%d\n", pkt.pts, ist->next_dts, pkt.stream_index);
					pkt.pts = AV_NOPTS_VALUE;
				}
			}
		}
	}

	if (pkt.dts != AV_NOPTS_VALUE)
		ifile->last_ts = av_rescale_q(pkt.dts, ist->st->time_base, { 1, AV_TIME_BASE });

	sub2video_heartbeat(ist, pkt.pts);

	process_input_packet(ist, &pkt);  //解码前数据AVPacket，解码后数据AVFrame

discard_packet:
	av_free_packet(&pkt);

	return 0;
}

/**
* Perform a step of transcoding for the specified filter graph.
*
* @param[in]  graph     filter graph to consider
* @param[out] best_ist  input stream where a frame would allow to continue
* @return  0 for success, <0 for error
*/
static int transcode_from_filter(FilterGraph *graph, InputStream **best_ist)
{
	int i, ret;
	int nb_requests, nb_requests_max = 0;
	InputFilter *ifilter;
	InputStream *ist;

	*best_ist = NULL;
	ret = avfilter_graph_request_oldest(graph->graph);
	if (ret >= 0)
		return reap_filters(0);

	if (ret == AVERROR_EOF) {
		ret = reap_filters(1);
		for (i = 0; i < graph->nb_outputs; i++)
			close_output_stream(graph->outputs[i]->ost);
		return ret;
	}
	if (ret != AVERROR(EAGAIN))
		return ret;

	for (i = 0; i < graph->nb_inputs; i++) {
		ifilter = graph->inputs[i];
		ist = ifilter->ist;
		if (input_files[ist->file_index]->eagain ||
			input_files[ist->file_index]->eof_reached)
			continue;
		nb_requests = av_buffersrc_get_nb_failed_requests(ifilter->filter);
		if (nb_requests > nb_requests_max) {
			nb_requests_max = nb_requests;
			*best_ist = ist;
		}
	}

	if (!*best_ist)
	for (i = 0; i < graph->nb_outputs; i++)
		graph->outputs[i]->ost->unavailable = 1;

	return 0;
}

/**
* Run a single step of transcoding.
*
* @return  0 for success, <0 for error
*/
static int transcode_step(void)
{
	OutputStream *ost;
	InputStream  *ist;
	int ret;

	ost = choose_output();    //选择一个有效的输出流进行处理
	if (!ost) {
		if (got_eagain()) {
			reset_eagain();
			av_usleep(10000);
			return 0;
		}
		av_log(NULL, AV_LOG_VERBOSE, "No more inputs to read from, finishing.\n");
		return AVERROR_EOF;
	}

	if (ost->filter) {//选择一个输入流
		if ((ret = transcode_from_filter(ost->filter->graph, &ist)) < 0)  //这个函数设置了线程个数5，
			return ret;
		if (!ist)
			return 0;
	}
	else {
		av_assert0(ost->source_index >= 0);
		ist = input_streams[ost->source_index];
	}

	//读取并处理每一个包
	ret = process_input(ist->file_index);  //file_index针对有多个输入文件的情况
	if (ret == AVERROR(EAGAIN)) {
		if (input_files[ist->file_index]->eagain)
			ost->unavailable = 1;
		return 0;
	}

	if (ret < 0)
		return ret == AVERROR_EOF ? 0 : ret;

	return reap_filters(0);   //根据滤波器做滤波处理，并把处理完的音视频输出到输出文件中,实际完成了编码封装的工作
}

/*
* The following code is the main loop of the file converter
*/
static int transcode(void)
{
	int ret, i;
	AVFormatContext *os;
	OutputStream *ost;
	InputStream *ist;
	int64_t timer_start;

	//设置编码参数，打开所有输出流的编码器，打开所有输入流的解码器，写入所有输出文件的文件头
	ret = transcode_init();
	if (ret < 0)
		goto fail;

	if (stdin_interaction) {
		av_log(NULL, AV_LOG_INFO, "Press [q] to stop, [?] for help\n");
	}

	timer_start = av_gettime_relative();

#if HAVE_PTHREADS
	if ((ret = init_input_threads()) < 0)
		goto fail;
#endif

	//循环，直到收到系统信号才退出
	while (!received_sigterm) {
		int64_t cur_time = av_gettime_relative();

		/* if 'q' pressed, exits */
		if (stdin_interaction)    //根据用户按下的ｑ键，进行退出程序的操作
		if (check_keyboard_interaction(cur_time) < 0)    //检测键盘操作，看是否按下Ｑ键
			break;

		/* check if there's any stream where output is still needed */
		if (!need_output()) {
			av_log(NULL, AV_LOG_VERBOSE, "No more output streams to write to, finishing.\n");
			break;
		}

		ret = transcode_step();
		if (ret < 0) {
			if (ret == AVERROR_EOF || ret == AVERROR(EAGAIN)) {
				continue;
			}
			else {
				char errbuf[128];
				av_strerror(ret, errbuf, sizeof(errbuf));

				av_log(NULL, AV_LOG_ERROR, "Error while filtering: %s\n", errbuf);
				break;
			}
		}

		/* dump report by using the output first video and audio streams */
		print_report(0, timer_start, cur_time);    //打印一些信息，输出到屏幕中
	}
#if HAVE_PTHREADS
	free_input_threads();
#endif

	/* at the end of stream, we must flush the decoder buffers
	* 文件处理完了，把缓冲内剩余的数据写到输出文件中*/
	for (i = 0; i < nb_input_streams; i++) {
		ist = input_streams[i];
		if (!input_files[ist->file_index]->eof_reached && ist->decoding_needed) {
			process_input_packet(ist, NULL);
		}
	}
	flush_encoders();    //输出编码器中的剩余的帧

	term_exit();

	/* write the trailer if needed and close file 为有需要的文件写文件结尾*/
	for (i = 0; i < nb_output_files; i++) {
		os = output_files[i]->ctx;
		av_write_trailer(os);
	}

	/* dump report by using the first video and audio streams */
	print_report(1, timer_start, av_gettime_relative());

	/* close each encoder 关闭编码器*/
	for (i = 0; i < nb_output_streams; i++) {
		ost = output_streams[i];
		if (ost->encoding_needed) {
			av_freep(&ost->enc_ctx->stats_in);
		}
	}

	/* close each decoder 关闭解码器*/
	for (i = 0; i < nb_input_streams; i++) {
		ist = input_streams[i];
		if (ist->decoding_needed) {
			avcodec_close(ist->dec_ctx);
			if (ist->hwaccel_uninit)
				ist->hwaccel_uninit(ist->dec_ctx);
		}
	}

	/* finished ! */
	ret = 0;

fail:
#if HAVE_PTHREADS
	free_input_threads();
#endif

	if (output_streams) {
		for (i = 0; i < nb_output_streams; i++) {
			ost = output_streams[i];
			if (ost) {
				if (ost->logfile) {
					fclose(ost->logfile);
					ost->logfile = NULL;
				}
				av_freep(&ost->forced_kf_pts);
				av_freep(&ost->apad);
				av_freep(&ost->disposition);
				av_dict_free(&ost->encoder_opts);
				av_dict_free(&ost->swr_opts);
				av_dict_free(&ost->resample_opts);
				av_dict_free(&ost->bsf_args);
			}
		}
	}
	return ret;
}


static int64_t getutime(void)
{
#if HAVE_GETRUSAGE
	struct rusage rusage;

	getrusage(RUSAGE_SELF, &rusage);
	return (rusage.ru_utime.tv_sec * 1000000LL) + rusage.ru_utime.tv_usec;
#elif HAVE_GETPROCESSTIMES
	HANDLE proc;
	FILETIME c, e, k, u;
	proc = GetCurrentProcess();
	GetProcessTimes(proc, &c, &e, &k, &u);
	return ((int64_t)u.dwHighDateTime << 32 | u.dwLowDateTime) / 10;
#else
	return av_gettime_relative();
#endif
}

static int64_t getmaxrss(void)
{
#if HAVE_GETRUSAGE && HAVE_STRUCT_RUSAGE_RU_MAXRSS
	struct rusage rusage;
	getrusage(RUSAGE_SELF, &rusage);
	return (int64_t)rusage.ru_maxrss * 1024;
#elif HAVE_GETPROCESSMEMORYINFO
	HANDLE proc;
	PROCESS_MEMORY_COUNTERS memcounters;
	proc = GetCurrentProcess();
	memcounters.cb = sizeof(memcounters);
	GetProcessMemoryInfo(proc, &memcounters, sizeof(memcounters));
	return memcounters.PeakPagefileUsage;
#else
	return 0;
#endif
}
static void log_callback_null(void *ptr, int level, const char *fmt, va_list vl)
{
}

int start_ffmpeg(int argc, char **argv)
{
	int ret;        //用於解析參數的返回值，根據返回值可判斷參數是否合理正確
	int64_t ti;
	//表示时间，用于计算编解码花费的时间

	register_exit(ffmpeg_cleanup);
	//释放空间，应该是在推出程序的时候调用，目前还没看出怎么用

	setvbuf(stderr, NULL, _IONBF, 0); /* win32 runtime needs this */
	/*
	* int setvbuf(FILE *stream,char *buf,int type,unsigned size);
	* type:期望缓冲区的类型，有下面三种
	* _IOFBF():当缓冲区为空时，从流读入数据；或者当缓冲区满时，向流写入数据
	* _IOLBF():每次从流中读入一行数据或向流写入一行数据
	* _IONBF():直接从流中读入数据或直接向流写入数据，没有缓冲区，这是上面代码的用法，在这里是
	* 直接将要输出的编解码内容写入到ｓｔｄｅｒｒ中，这里没有定义缓冲区
	* size:缓冲区内字节的数量
	*/

	av_log_set_flags(AV_LOG_SKIP_REPEATED);
	/*
	* AV_LOG_SKIP_REPEATED 在log.h中定义，值为１，允许跳过重复的消息，使用日志av_log()
	*/


	if (argc>1 && !strcmp(argv[1], "-d")){
		run_as_daemon = 1;
		av_log_set_callback(log_callback_null);
		argc--;
		argv++;
	}

	//avcodec_register_all();
	//在allcodecs.c中定义
	//注册硬件加速器，视频编解码器，音频编解码器,PCM/DPCM/ADPCM编解码器，字幕，解析器，比特流滤波器等
#if CONFIG_AVDEVICE
	avdevice_register_all();
	//在alldevices.c中定义，用于一些设备注册，如摄像头等设备资源
	//
#endif
	//avfilter_register_all();
	//滤波器注册,在allfilters.c中定义

	//av_register_all();
	//也是实现注册的，和avcodec_register_all()共用一个变量，添加了一些封装格式的注册

	//avformat_network_init();
	//当需要播放网络流时，这个函数就是用来处理相关信息的，在libavformat/utils.c中定义

	//term_init();
	//ｌｉｎｕｘ中对串口模式的定义，好像是对键盘输入方式做个定义

	/* parse options and open all input/output files */
	ret = ffmpeg_parse_options(argc, argv);
	//解析参数，在ffmpeg_opt.c中定义
	if (ret < 0)
		exit_program(1);
	/*这个函数就是调用ffmpeg_cleanup，在上面register_exit有说明*/

	if (nb_output_files <= 0 && nb_input_files == 0) {  //没有输入文件和输出文件即退出
		show_usage();
		av_log(NULL, AV_LOG_WARNING, "Use -h to get full help or, even better, run 'man %s'\n", program_name);
		exit_program(1);
	}

	/* file converter / grab */
	if (nb_output_files <= 0) {
		av_log(NULL, AV_LOG_FATAL, "At least one output file must be specified\n");
		exit_program(1);
	}

	//     if (nb_input_files == 0) {
	//         av_log(NULL, AV_LOG_FATAL, "At least one input file must be specified\n");
	//         exit_program(1);
	//     }

	current_time = ti = getutime();
	/*记录下当前时间*/
	if (transcode() < 0)
		exit_program(1);
	ti = getutime() - ti;
	/*减去编解码之前记录的时间，从而得出编解码所用的时间，在Console中输出时间*/

	if (do_benchmark) {
		av_log(NULL, AV_LOG_INFO, "bench: utime=%0.3fs\n", ti / 1000000.0);
	}
	av_log(NULL, AV_LOG_DEBUG, "%I64d frames successfully decoded, %I64d decoding errors\n",
		decode_error_stat[0], decode_error_stat[1]);
	if ((decode_error_stat[0] + decode_error_stat[1]) * max_error_rate < decode_error_stat[1])
		exit_program(69);

	exit_program(received_nb_signals ? 255 : main_return_code);
	return main_return_code;
}


int videoIncreaseNum = 0;       //视频处理后递增的编号，eg：[v3]
int audioIncreaseNum = 0;
int concatVideoCount = 0;
int concatAudioCount = 0;
char **concatVideoInfo = NULL;           //存放需要进行连接的视频，好像没用，有待检查
char **concatAudioInfo = NULL;           //存放需要进行连接的音频

videoUsedInfo* m_videoUsedInfo;         //全局视频使用信息结构体数组，数组大小为输入视频的个数

//举例，传入3个视频，分别是v1、v2和v3，其中视频v1采用淡入特效，从0秒开始，持续2秒，v1和v2之间采用交叉叠化特效，交叉时间3秒，v2和v3之间采用自动揭开特效，从10秒开始，持续时间4秒，最后输出视频out4，视频编码为libx264，音频编码为mp2，视频分辨率1920x1080。由此传入参数为
//video_path[10] = { v1, v2, v3 }；
//specialEffect[10] = { { 1, fade, in, 0, 2, 1, 1 }, { 2, cross, -1, 0, 3, 1, 2 }, { 3, discover, -1, 10, 4, 2, 3 } }；
//outputParam = { out4，libx264，mp2, 1920x1080 }。

/*  argc=20   argv
E:\vcworkspace\mergevideo\debug\mergevideo.exe
-i
e:/video/gaoqing_mpeg2.ts
-i
e:/video/gaoqing_mpeg2.ts
-i
e:/video/Titanic.ts
-filter_complex
"[0:v]setdar=16/9,scale=w=1920:h=1080,trim=start=0:end=38[v0];
[1:v]setdar=16/9,scale=w=1920:h=1080,trim=start=38:end=41,setpts=PTS-STARTPTS[v1];
[2:v]setdar=16/9,scale=w=1920:h=1080 [v2];
[v2][v1]blend=all_expr='A*(if(gte(T,3),1,T/3))+B*(1-(if(gte(T,3),1,T/3)))'[v3];
[0:a]atrim=start=0:end=38[a0];
[2:a]afade=in:st=0:d=1[a2];
[v0] [a0] [v3] [a2] concat=n=2:v=1:a=1 [v] [a]"
-map
[v]
-map
[a]
-vcodec
mpeg2video
-acodec
aac
-strict
-2
filter_1920_1080.ts
*/

void CheckScale(char *videoScale, int* w, int* h)
{
	/*检查是否传入分辨率参数，如果传入，按该参数走，没有传入，默认高清参数1920x1080*/
	char * temp = NULL;   //中间变量
	int i = 1;
	char ap[9];

	char c[4] = "*Xx";
	temp = strchr(videoScale, c[0]);

	while (i < 3 && temp == NULL)
	{
		temp = strchr(videoScale, c[i++]);
	}
	if (temp == NULL)
	{
		*w = 1920;
		*h = 1080;
		return;   //视频宽高不对,设置为默认高清视频
	}

	int pos = temp - videoScale;   //*1080
	strncpy(ap, videoScale, pos);
	ap[pos] = 0;
	*w = atoi(ap);   //1920

	i = 0;
	temp = temp + 1;
	while (ap[i++] = *(temp++));
	ap[i] = 0;
	*h = atoi(ap);
}
char * StartVideo(int startVideoID, int type)    //传入的编号视频1值为1 type标记是否必须使用视频原编号
{
	/*返回 [0:v] 这部分内容，有可能返回结果是已经产生的视频序号，如[v2]*/
	char * temp = NULL;
	temp = (char*)calloc(256, sizeof(char));

	if (type == 1)
		sprintf(temp, "%s%d%s", "[", startVideoID - 1, ":v]");  //连接字符串
	else{
		if (m_videoUsedInfo[startVideoID - 1].tailUsedorNot)  //先判断传入的头视频的尾部是否使用
			sprintf(temp, "%s", m_videoUsedInfo[startVideoID - 1].tailID);
		else if (m_videoUsedInfo[startVideoID - 1].headUsedorNot)
			sprintf(temp, "%s", m_videoUsedInfo[startVideoID - 1].headID);
		else
			sprintf(temp, "%s%d%s", "[", startVideoID - 1, ":v]");  //连接字符串
	}

	return temp;

}
char * StartAudio(int startAudioID)
{
	/*返回 [0:a] 这部分内容*/
	char * temp = NULL;
	temp = (char*)calloc(256, sizeof(char));

	if (m_videoUsedInfo[startAudioID - 1].audioUsedorNot)
		sprintf(temp, "%s", m_videoUsedInfo[startAudioID - 1].audioID);
	else
		sprintf(temp, "%s%d%s", "[", startAudioID - 1, ":a]");  //连接字符串

	return temp;

}
int gcd(int m, int n)//求n和m的最大公约数
{
	int min = m>n ? n : m; //两个数的较小者。
	while (min > 0)
	{
		if (m%min == 0 && n%min == 0) break;//都能整除，则为最大公约数。
		min--;
	}
	return min;
}

char * SetDar(int w, int h)
{
	/*返回setdar scale 这部分内容*/
	char * temp = NULL;
	temp = (char*)calloc(256, sizeof(char));

	int wh_gcd = gcd(w, h);

	sprintf(temp, "%s%d%s%d%s%d%s%d",
		"setdar=",
		w / wh_gcd,
		"/",
		h / wh_gcd,
		",scale=w=",
		w,
		":h=",
		h);  //连接字符串

	return temp;
}

//获得特效处理后的视频编号[v0],[v1]等
char * GetVideoIncrease()
{
	char *videoIncreaseString = NULL;     //用于结尾的视频号递增
	videoIncreaseString = (char*)calloc(3, sizeof(char));

	sprintf(videoIncreaseString, "%s%d%s", "[v", videoIncreaseNum++, "]");

	return videoIncreaseString;
}

//获得特效处理后的音频编号[a0],[a1]等
char * GetAudioIncrease()
{
	char *audioIncreaseString = NULL;     //用于结尾的视频号递增
	audioIncreaseString = (char*)calloc(3, sizeof(char));

	sprintf(audioIncreaseString, "%s%d%s", "[a", audioIncreaseNum++, "]");

	return audioIncreaseString;
}

//淡入淡出
char* FadeCommand(specialEffect mSpecialEffect, int w, int h)
{
	char * videoEffect = NULL;
	videoEffect = (char*)calloc(256, sizeof(char));
	char * fadestring = NULL;
	fadestring = (char*)calloc(256, sizeof(char));
	char *type = NULL;
	type = (char*)calloc(3, sizeof(char));
	char * increaseVideoID = NULL;     //存放这个视频处理后的视频序号，最后放入视频队列中，先进先出
	increaseVideoID = (char*)calloc(10, sizeof(char));
	char * error = NULL;               //存放返回的错误信息
	error = (char*)calloc(256, sizeof(char));

	//判断特效类型，淡入特效则视频头还没用，淡出特效则视频尾还没用
	if (mSpecialEffect.type == 1 && m_videoUsedInfo[mSpecialEffect.forwardVideoID].tailUsedorNot == 0)      //淡出特效
		type = "out";
	else if (mSpecialEffect.type == 0 && m_videoUsedInfo[mSpecialEffect.forwardVideoID].headUsedorNot == 0)
		type = "in";
	else
	{
		error = "fade type is error!!!";
		//退出总程序，返回错误信息。
	}

	increaseVideoID = GetVideoIncrease();
	sprintf(fadestring, "%s%s%s%d%s%d%s",
		"fade=t=",
		type,
		":st=",
		mSpecialEffect.startTime,
		":d=",
		mSpecialEffect.duration,
		increaseVideoID);

	//将产生的处理后的视频编号放入队列中，先进先出
	concatVideoInfo[concatVideoCount++] = increaseVideoID;
	//淡入淡出音频不动，将音频编号放入队列中，先进先出
	concatAudioInfo[concatAudioCount++] = StartAudio(mSpecialEffect.forwardVideoID);

	//strcat(videoEffect, StartVideo(mSpecialEffect.forwardVideoID));
	sprintf(videoEffect, "%s%s%s%s%s",
		StartVideo(mSpecialEffect.forwardVideoID, 0),
		SetDar(w, h),
		",",
		fadestring,
		";");  //连接字符串

	if (mSpecialEffect.type == 1)   //淡出编号放在尾部
	{
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailID, increaseVideoID);
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioID, StartAudio(mSpecialEffect.forwardVideoID));
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailUsedorNot = 1;
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioUsedorNot = 1;
	}
	else                //淡入编号放在头部
	{
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headID, increaseVideoID);
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioID, StartAudio(mSpecialEffect.forwardVideoID));
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headUsedorNot = 1;
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioUsedorNot = 1;
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headSpecialEffectID = 1;
	}

	return videoEffect;
}

int GetVideoTotalTime(char * videoPath)     //返回视频总时长，到秒
{
	int videoTotalTime = 40;
	int ret, i, video_index;
	AVFormatContext *ifmt_ctx = NULL;

	if ((ret = avformat_open_input(&ifmt_ctx, videoPath, NULL, NULL)) < 0) {
		av_log(NULL, AV_LOG_ERROR, "Cannot openinput file\n");
		return ret;
	}
	if ((ret = avformat_find_stream_info(ifmt_ctx, NULL))< 0) {
		av_log(NULL, AV_LOG_ERROR, "Cannot findstream information\n");
		return ret;
	}

	//获得视频流的号
	for (i = 0; i < ifmt_ctx->nb_streams; i++)
	{
		if (ifmt_ctx->streams[i]->codec->codec_type == AVMEDIA_TYPE_VIDEO){
			video_index = i;
			break;
		}
	}
	if (video_index < 0)
		return -1;

	videoTotalTime = (int)(ifmt_ctx->streams[video_index]->duration * ifmt_ctx->streams[video_index]->time_base.num) / ifmt_ctx->streams[video_index]->time_base.den;

	avformat_free_context(ifmt_ctx);

	return videoTotalTime;
}

//交叉叠化
char* DissolveCommand(specialEffect mSpecialEffect, char* videoPath, int w, int h)
{
	char * videoEffect = NULL;     //存放最后的总参数
	videoEffect = (char*)calloc(256, sizeof(char));

	char * forwardVideo1 = NULL;    //处理第一个视频的不交叉部分
	forwardVideo1 = (char*)calloc(256, sizeof(char));

	char * forwardAudio = NULL;
	forwardAudio = (char*)calloc(256, sizeof(char));

	char * forwardVideo2 = NULL;
	forwardVideo2 = (char*)calloc(256, sizeof(char));
	char * forwardVideoID = NULL;     //存放这个视频处理后的视频序号，留待交叉叠化的时候用
	forwardVideoID = (char*)calloc(10, sizeof(char));

	char * backwardVideo = NULL;
	backwardVideo = (char*)calloc(256, sizeof(char));
	char * backwardVideoID = NULL;     //存放这个视频处理后的视频序号，留待交叉叠化的时候用
	backwardVideoID = (char*)calloc(10, sizeof(char));

	char * dissolveEffect = NULL;
	dissolveEffect = (char*)calloc(256, sizeof(char));

	char * error = NULL;        //存放返回的错误信息，用于整个程序的退出
	error = (char*)calloc(256, sizeof(char));

	char * increaseID = NULL;     //存放可能放入队列中的音视频编号，先进先出
	increaseID = (char*)calloc(10, sizeof(char));
	char * startID = NULL;     //这是为了统一forwardvideo的两部分处理头视频相同
	startID = (char*)calloc(10, sizeof(char));

	int type = 0;
	int videoTotalTime = GetVideoTotalTime(videoPath);   //获得视频总时长，秒

	if (mSpecialEffect.forwardVideoID + 1 != mSpecialEffect.backwardVideoID)
	{
		//不是前后视频，不可能交叉叠化
		error = "dissolve videoID is not right!!!";
		//退出整个程序
	}

	//[0:v]setdar=16/9,scale=w=1920:h=1080,trim=start=0:end=38[v0];
	increaseID = GetVideoIncrease();
	startID = StartVideo(mSpecialEffect.forwardVideoID, type);
	sprintf(forwardVideo1, "%s%s%s%d%s%s",
		startID,
		SetDar(w, h),
		",trim=start=0:end=",
		videoTotalTime - mSpecialEffect.duration + 1,
		increaseID,
		";"
		);

	//将产生的处理后的视频编号放入队列中，先进先出
	concatVideoInfo[concatVideoCount++] = increaseID;
	//将产生的处理后的视频编号放入前一个视频的尾部
	if (m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailUsedorNot == 0)
	{
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailID, increaseID);
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailUsedorNot = 1;
	}
	else
	{
		error = "dissolve forwardvideo is used!!!";
		//退出整个程序
	}

	//[0:a]atrim=start=0:end=38[a0];
	increaseID = GetAudioIncrease();
	sprintf(forwardAudio, "%s%s%d%s%s",
		StartAudio(mSpecialEffect.forwardVideoID),
		"atrim=start=0:end=",
		videoTotalTime - mSpecialEffect.duration + 1,
		increaseID,
		";"
		);

	//将音频编号放入队列中，先进先出
	//concatAudioInfo[concatAudioCount++] = increaseID;
	//将编码后的音频信息放入前一个视频的音频编号
	strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioID, increaseID);
	m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioUsedorNot = 1;

	//[1:v]setdar=16/9,scale=w=1920:h=1080,trim=start=38:end=41,setpts=PTS-STARTPTS[v1];
	if (m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headSpecialEffectID == 2 ||
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headSpecialEffectID == 3)
	{
		type = 1;
		startID = StartVideo(mSpecialEffect.forwardVideoID, type);
		type = 0;   //type复位
	}

	forwardVideoID = GetVideoIncrease();
	sprintf(forwardVideo2, "%s%s%s%d%s%d%s%s%s",
		startID,
		SetDar(w, h),
		",trim=start=",
		videoTotalTime - mSpecialEffect.duration + 1,
		":end=",
		videoTotalTime + 1,
		",setpts=PTS-STARTPTS",
		forwardVideoID,
		";"
		);

	//[2:v]setdar=16/9,scale=w=1920:h=1080 [v2];
	backwardVideoID = GetVideoIncrease();
	sprintf(backwardVideo, "%s%s%s%s",
		StartVideo(mSpecialEffect.backwardVideoID, type),
		SetDar(w, h),
		backwardVideoID,
		";"
		);

	//[v2][v1]blend=all_expr='A*(if(gte(T,3),1,T/3))+B*(1-(if(gte(T,3),1,T/3)))'[v3]; 
	increaseID = GetVideoIncrease();
	sprintf(dissolveEffect, "%s%s%s%d%s%d%s%d%s%d%s%s%s",
		backwardVideoID,
		forwardVideoID,
		"blend=all_expr='A*(if(gte(T,",
		mSpecialEffect.duration,
		"),1,T/",
		mSpecialEffect.duration,
		"))+B*(1-(if(gte(T,",
		mSpecialEffect.duration,
		"),1,T/",
		mSpecialEffect.duration,
		")))'",
		increaseID,
		";"
		);
	//将产生的处理后的视频编号放入队列中，先进先出
	//concatVideoInfo[concatVideoCount++] = increaseID;
	//将音频编号放入队列中，先进先出
	//concatAudioInfo[concatAudioCount++] = StartAudio(mSpecialEffect.backwardVideoID);

	//处理后一个视频的头部使用情况
	if (m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headUsedorNot == 0)
	{
		m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headSpecialEffectID = 2;
		strcpy(m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headID, increaseID);
		strcpy(m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].audioID, StartAudio(mSpecialEffect.backwardVideoID));
		m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headUsedorNot = 1;
		m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].audioUsedorNot = 1;
	}
	else
	{
		error = "dissolve backwordvideo is used!!!";
		//退出整个程序
	}

	sprintf(videoEffect, "%s%s%s%s%s",
		forwardVideo1,
		forwardAudio,
		forwardVideo2,
		backwardVideo,
		dissolveEffect
		);

	return videoEffect;
}

//自动揭开
char* RevealCommand(specialEffect mSpecialEffect, char* videoPath, int w, int h)
{
	char * videoEffect = NULL;     //存放最后的总参数
	videoEffect = (char*)calloc(256, sizeof(char));

	char * revealEffect = NULL;
	revealEffect = (char*)calloc(256, sizeof(char));

	char * forwardVideo1 = NULL;    //处理第一个视频的不揭开部分
	forwardVideo1 = (char*)calloc(256, sizeof(char));

	char * forwardAudio = NULL;      //处理第一个文件的音频部分
	forwardAudio = (char*)calloc(256, sizeof(char));

	char * forwardVideo2 = NULL;     //处理第一个视频的揭开部分
	forwardVideo2 = (char*)calloc(256, sizeof(char));

	char * forwardVideoID = NULL;     //存放这个视频处理后的视频序号，留待交叉叠化的时候用
	forwardVideoID = (char*)calloc(10, sizeof(char));

	char * backwardVideo = NULL;
	backwardVideo = (char*)calloc(256, sizeof(char));

	char * backwardVideoID = NULL;     //存放这个视频处理后的视频序号，留待交叉叠化的时候用
	backwardVideoID = (char*)calloc(10, sizeof(char));

	char * increaseID = NULL;     //存放可能放入队列中的音视频编号，先进先出
	increaseID = (char*)calloc(10, sizeof(char));
	char * startID = NULL;     //这是为了统一forwardvideo的两部分处理头视频相同
	startID = (char*)calloc(10, sizeof(char));

	int type = 0;
	int videoTotalTime = GetVideoTotalTime(videoPath);   //获得视频总时长，秒

	if (mSpecialEffect.forwardVideoID + 1 != mSpecialEffect.backwardVideoID)
	{
		//不是前后视频，不可能自动揭开
		videoEffect = "dissolve videoID is not right!!!";
		//退出整个程序
	}

	//[0:v]setdar=16/9,scale=w=1920:h=1080,trim=start=0:end=38[v0];
	increaseID = GetVideoIncrease();
	startID = StartVideo(mSpecialEffect.forwardVideoID, type);
	sprintf(forwardVideo1, "%s%s%s%d%s%s",
		startID,
		SetDar(w, h),
		",trim=start=0:end=",
		videoTotalTime - mSpecialEffect.duration + 1,
		increaseID,
		";"
		);

	//将产生的处理后的视频编号放入前一个视频的尾部
	if (m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailUsedorNot == 0)
	{
		strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailID, increaseID);
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].tailUsedorNot = 1;
	}
	else
	{
		videoEffect = "reveal forwardvideo is used!!!";
		return videoEffect;
		//退出整个程序
	}

	//[0:a]atrim=start=0:end=38[a0];
	increaseID = GetAudioIncrease();
	sprintf(forwardAudio, "%s%s%d%s%s",
		StartAudio(mSpecialEffect.forwardVideoID),
		"atrim=start=0:end=",
		videoTotalTime - mSpecialEffect.duration + 1,
		increaseID,
		";"
		);

	//将编码后的音频信息放入前一个视频的音频编号
	strcpy(m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioID, increaseID);
	m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].audioUsedorNot = 1;

	//[1:v]setdar=16/9,scale=w=1920:h=1080,trim=start=38:end=41,setpts=PTS-STARTPTS[v1];
	if (m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headSpecialEffectID == 2 ||
		m_videoUsedInfo[mSpecialEffect.forwardVideoID - 1].headSpecialEffectID == 3)
	{
		type = 1;
		startID = StartVideo(mSpecialEffect.forwardVideoID, type);
		type = 0;
	}

	forwardVideoID = GetVideoIncrease();   //记录下最后形成的编码，留待blend中用
	sprintf(forwardVideo2, "%s%s%s%d%s%d%s%s%s",
		startID,
		SetDar(w, h),
		",trim=start=",
		videoTotalTime - mSpecialEffect.duration + 1,
		":end=",
		videoTotalTime + 1,
		",setpts=PTS-STARTPTS",
		forwardVideoID,
		";"
		);

	//[2:v]setdar=16/9,scale=w=1920:h=1080 [v2];
	backwardVideoID = GetVideoIncrease();   //记录下最后形成的编码，留待blend中用
	sprintf(backwardVideo, "%s%s%s%s",
		StartVideo(mSpecialEffect.backwardVideoID, type),
		SetDar(w, h),
		backwardVideoID,
		";"
		);

	//[v2][v1]blend=all_expr='if(gte(T*SW*1000+X,W),A,B)'[v3]
	increaseID = GetVideoIncrease();     //留下最后形成的编码，放入后一个视频的头部编号去
	sprintf(revealEffect, "%s%s%s%s%s",
		backwardVideoID,
		forwardVideoID,
		"blend=all_expr='if(gte(T*SW*1000+X,W),A,B)'",
		increaseID,
		";"
		);

	//处理后一个视频的头部使用情况
	if (m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headUsedorNot == 0)
	{
		m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headSpecialEffectID = 3;
		strcpy(m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headID, increaseID);
		m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].headUsedorNot = 1;
	}
	else
	{
		videoEffect = "reveal backwordvideo is used!!!";
		return videoEffect;
		//退出整个程序
	}

	strcpy(m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].audioID, StartAudio(mSpecialEffect.backwardVideoID));
	m_videoUsedInfo[mSpecialEffect.backwardVideoID - 1].audioUsedorNot = 1;

	sprintf(videoEffect, "%s%s%s%s%s",
		forwardVideo1,
		forwardAudio,
		forwardVideo2,
		backwardVideo,
		revealEffect
		);

	return videoEffect;
}

char* ConcatCommand(int videoCount)
{
	// [v0] [a0] [v3] [a2] concat=n=2:v=1:a=1 [v] [a]
	int i;
	char *concatInfo = NULL;//用于组织特效的参数
	concatInfo = (char*)calloc(256, sizeof(char));

	for (i = 0; i < videoCount; i++)
	{
		sprintf(concatInfo, "%s %s %s ",
			concatInfo,
			m_videoUsedInfo[i].tailUsedorNot ? m_videoUsedInfo[i].tailID : m_videoUsedInfo[i].headID,
			m_videoUsedInfo[i].audioID);
	}

	sprintf(concatInfo, "%s%s%d%s",
		concatInfo,
		"concat=n=",
		videoCount,
		":v=1:a=1 [v] [a]");

	return concatInfo;
}

char* mergeCommand(int videoID, int w, int h)
{
	//[3:v]setdar=16/9,scale=w=1920:h=1080,[v5]
	char *mergeInfo = NULL;//用于组织特效的参数
	mergeInfo = (char*)calloc(256, sizeof(char));
	char * increaseID = NULL;     //存放可能放入队列中的音视频编号，先进先出
	increaseID = (char*)calloc(10, sizeof(char));
	int type = 0;

	increaseID = GetVideoIncrease();
	sprintf(mergeInfo, "%s%s%s%s",
		StartVideo(videoID + 1, type),
		SetDar(w, h),
		increaseID,
		";");

	if (m_videoUsedInfo[videoID].headUsedorNot == 0)
	{
		strcpy(m_videoUsedInfo[videoID].headID, increaseID);
		strcpy(m_videoUsedInfo[videoID].audioID, StartAudio(videoID + 1));
		m_videoUsedInfo[videoID].headUsedorNot = 1;
		m_videoUsedInfo[videoID].audioUsedorNot = 1;
	}

	return mergeInfo;
}
char* MergeVideoSpecialEffectInterface(char* videoPath[], int videoCount, specialEffect mSpecialEffect[], int specialEffectCount, outputParam mOutputParam)
{
	char error[255] = "error";   //用于返回错误信息
	int argc = 1;                //参数个数
	int i, j;                    //中间变量
	char **argv = NULL;           //参数信息，传给ffmpeg主函数
	char *videoEffectInfo = NULL;//用于组织特效的参数
	char *videoEffectTemp = NULL;//用于组织特效的中间参数
	int w = 0, h = 0;

	avcodec_register_all();
	avfilter_register_all();
	//滤波器注册,在allfilters.c中定义

	av_register_all();
	//也是实现注册的，和avcodec_register_all()共用一个变量，添加了一些封装格式的注册

	avformat_network_init();
	//当需要播放网络流时，这个函数就是用来处理相关信息的，在libavformat/utils.c中定义

	term_init();
	//ｌｉｎｕｘ中对串口模式的定义，好像是对键盘输入方式做个定义

	argv = (char**)calloc(128, sizeof(char*));    //暂定参数最多128个，这个128回头预先定义

	for (i = 0; i < 128; ++i)
	{
		argv[i] = (char*)calloc(256, sizeof(char));    //每个参数最多可存放256个字符
	}

	concatVideoInfo = (char**)calloc(15, sizeof(char*));    //暂定可连接的视频最多15个
	concatAudioInfo = (char**)calloc(15, sizeof(char*));    //暂定可连接的音频最多15个

	for (i = 0; i < 15; ++i)
	{
		concatVideoInfo[i] = (char*)calloc(10, sizeof(char));    //视频的表示字符最多10个
		concatAudioInfo[i] = (char*)calloc(10, sizeof(char));    //音频的表示字符最多10个
	}

	videoEffectInfo = (char*)calloc(10240, sizeof(char));
	videoEffectTemp = (char*)calloc(10240, sizeof(char));

	//sprintf(videoEffectInfo, "%s", "\"");

	//判断传入视频的个数是否合理，最大值为20
	for (i = 0; i < videoCount; i++)
	{
		//checkvideoinfo();检查输入视频路径是否正确，视频内容是否完整，错误则退出，正确则进行下一步
		//考虑正确性
		argv[argc++] = "-i";
		strcpy(argv[argc++], videoPath[i]);
	}

	//对每个输入的视频，初始化对应的结构体videoUsedInfo
	m_videoUsedInfo = (videoUsedInfo*)malloc(videoCount*sizeof(videoUsedInfo));

	for (i = 0; i < videoCount; i++)    //初始化
	{
		memset(m_videoUsedInfo[i].headID, '\0', 10);
		m_videoUsedInfo[i].headUsedorNot = 0;
		memset(m_videoUsedInfo[i].tailID, '\0', 10);
		m_videoUsedInfo[i].tailUsedorNot = 0;
		memset(m_videoUsedInfo[i].audioID, '\0', 10);
		m_videoUsedInfo[i].audioUsedorNot = 0;
		m_videoUsedInfo[i].headSpecialEffectID = -1;
	}

	if (specialEffectCount == 0)   //当特效个数为0，单纯的合并视频
	{
		if (mOutputParam.videoScale)   //这个的值是1920的1，需要调整
			CheckScale(mOutputParam.videoScale, &w, &h);
		//videoEffectTemp = ;   //仅仅合并视频
	}

	for (i = 0; i < specialEffectCount; i++)
	{
		if (mOutputParam.videoScale)   //这个的值是1920的1，需要调整
			CheckScale(mOutputParam.videoScale, &w, &h);

		//检查特效设置的合理性
		switch (mSpecialEffect[i].id)
		{
		case 0:break;          //特效id，其中0表示空，没有特效
		case 1:videoEffectTemp = FadeCommand(mSpecialEffect[i], w, h); //1表示淡入淡出fade
			break;
		case 2:videoEffectTemp = DissolveCommand(mSpecialEffect[i], videoPath[mSpecialEffect[i].forwardVideoID - 1], w, h);//2表示交叉叠化cross
			break;
		case 3:videoEffectTemp = RevealCommand(mSpecialEffect[i], videoPath[mSpecialEffect[i].forwardVideoID - 1], w, h);//3表示自动揭开discover
			break;
		default:    //应该加入单纯合并视频的代码
			break;
		}
		sprintf(videoEffectInfo, "%s%s",
			videoEffectInfo,
			videoEffectTemp);
	}

	for (i = 0; i < videoCount; i++)    //判断是否有视频完全没有采用特效，那就直接合并视频
	{
		if (m_videoUsedInfo[i].headUsedorNot == 0 && m_videoUsedInfo[i].tailUsedorNot == 0)
		{
			videoEffectTemp = mergeCommand(i, w, h);

			sprintf(videoEffectInfo, "%s%s",
				videoEffectInfo,
				videoEffectTemp);
		}
	}

	//加入合并视频的信息[v0] [a0] [v3] [a2] concat=n=2:v=1:a=1 [v] [a]
	sprintf(videoEffectInfo, "%s%s",
		videoEffectInfo,
		ConcatCommand(videoCount));
	//	"\"");

	//videoEffectInfo = "effect";
	argv[argc++] = "-filter_complex";
	argv[argc++] = videoEffectInfo;
	argv[argc++] = "-map";
	argv[argc++] = "[v]";
	argv[argc++] = "-map";
	argv[argc++] = "[a]";
	if (mOutputParam.videoCodec)
	{
		argv[argc++] = "-vcodec";
		argv[argc++] = mOutputParam.videoCodec;
	}
	if (mOutputParam.audioCodec)
	{
		argv[argc++] = "-acodec";
		argv[argc++] = mOutputParam.audioCodec;
		if (strcmp(mOutputParam.audioCodec, "aac") == 0)   //两个字符串相同
		{
			argv[argc++] = "-strict";
			argv[argc++] = "-2";
		}
	}
	if (mOutputParam.videoScale)
	{
		argv[argc++] = "-s";
		argv[argc++] = mOutputParam.videoScale;
	}
	argv[argc++] = mOutputParam.outputVideoName;

	for (i = 1; i < argc; i++)
		printf("%d  %s\n", i, argv[i]);

	start_ffmpeg(argc, argv);

	return error;
}